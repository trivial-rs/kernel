use crate::error::Kind;
use crate::verifier::store::StorePointer;
use crate::verifier::stream;
use crate::verifier::CommandStream;
use crate::verifier::State;
use crate::verifier::StoreElement;
use crate::verifier::Table;
use crate::verifier::TableLike;
use crate::verifier::Term;
use crate::verifier::Type;
use crate::TResult;
use crate::Verifier;

#[derive(Copy, Clone, PartialEq)]
pub enum Opcode {
    End,
    Sort,
    TermDef,
    AxiomThm,
}

pub struct Command {
    opcode: Opcode,
}

fn allocate_var(proof_heap: &mut Heap, store: &mut Store, x: (usize, &Type)) {
    let var = StoreElement::Var {
        ty: *x.1,
        var: x.0 as u16,
    };

    let ptr = store.push(var);
    proof_heap.push(ptr);
}

fn binder_check<'a, T: TableLike<'a>>(table: &'a T, ty: Type, bv: &mut u64) -> TResult {
    let sort = table.get_sort(ty.get_sort()).ok_or(Kind::InvalidSort)?;
    let deps = ty.get_deps();

    if ty.is_bound() {
        if sort.is_strict() {
            return Err(Kind::SortIsStrict);
        }

        if deps != *bv {
            return Err(Kind::BindDep);
        }

        *bv *= 2;
    } else {
        if deps & !(*bv - 1) != 0 {
            return Err(Kind::BindDep);
        }
    }

    Ok(())
}

fn load_args(state: &mut State, table: &Table, binders: &[Type]) -> TResult {
    state.proof_heap.clear();

    let mut next_bv = 1;

    for (i, ty) in binders.iter().enumerate() {
        binder_check(table, *ty, &mut next_bv)?;
        allocate_var(&mut state.proof_heap, &mut state.store, (i, ty));
    }

    state.next_bv = next_bv;

    Ok(())
}

pub trait Statement {
    fn term_def(&mut self, idx: u32) -> TResult;

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult;
}

pub enum TermDef<'a, S, C, T>
where
    S: Iterator,
    S::Item: TryInto<stream::proof::Command>,
    C: CommandStream<'a>,
    T: TableLike<'a, Iterator = C::Iterator>,
{
    Start {
        idx: u32,
        stream: S,
    },
    RunProof {
        stepper: stream::proof::Stepper<'a, S, C, T>,
        ret_type: Type,
        term: &'a T::Term,
    },
    ProofDone {
        ret_type: Type,
        term: &'a T::Term,
    },
    RunUnify {
        stepper: stream::unify::Stepper<C::Iterator>,
    },
    Done,
}

use std::convert::TryInto;

impl<'a, S, C, T> TermDef<'a, S, C, T>
where
    S: Iterator,
    S::Item: TryInto<stream::proof::Command>,
    C: CommandStream<'a>,
    T: TableLike<'a, Iterator = C::Iterator>,
{
    pub fn new(idx: u32, stream: S) -> TermDef<'a, S, C, T> {
        TermDef::Start { idx, stream }
    }

    pub fn step(self, state: &mut State, table: &'a T) -> TResult<TermDef<'a, S, C, T>> {
        let next = match self {
            TermDef::Start { idx, stream } => {
                let term = table.get_term(idx).ok_or(Kind::InvalidTerm)?;
                let sort = table.get_sort(term.get_sort()).ok_or(Kind::InvalidSort)?;

                if sort.is_pure() {
                    return Err(Kind::SortIsPure);
                }

                let binders = term.get_binders();

                state.proof_heap.clear();

                let mut next_bv = 1;

                for (i, ty) in binders.iter().enumerate() {
                    binder_check(table, *ty, &mut next_bv)?;

                    allocate_var(&mut state.proof_heap, &mut state.store, (i, ty));
                }

                let ret_type = term.get_return_type();

                binder_check(table, ret_type, &mut next_bv)?;

                allocate_var(
                    &mut state.proof_heap,
                    &mut state.store,
                    (binders.len(), &ret_type),
                );

                state.next_bv = next_bv;

                if term.get_sort() != ret_type.get_sort() {
                    return Err(Kind::BadReturnType);
                }

                // todo: check if allocation of return var is necessary
                state.proof_heap.pop();

                if term.is_definition() {
                    TermDef::Done
                } else {
                    let stepper = stream::proof::Stepper::new(table, true, stream);

                    TermDef::RunProof {
                        stepper,
                        ret_type,
                        term,
                    }
                }
            }
            TermDef::RunProof {
                mut stepper,
                ret_type,
                term,
            } => match stepper.step(state) {
                Some(_) => TermDef::RunProof {
                    stepper,
                    ret_type,
                    term,
                },
                None => TermDef::ProofDone { ret_type, term },
            },
            TermDef::ProofDone { ret_type, term } => {
                if state.proof_stack.len() != 1 {
                    return Err(Kind::StackHasMoreThanOne);
                }

                let expr = state
                    .proof_stack
                    .pop()
                    .ok_or(Kind::Impossible)?
                    .as_expr()
                    .ok_or(Kind::InvalidStoreExpr)?;

                let ty = state
                    .store
                    .get_type_of_expr(expr)
                    .ok_or(Kind::InvalidStoreType)?;

                if !ty.is_compatible_to(&ret_type) {
                    return Err(Kind::TypeError);
                }

                if ty.get_deps() != ret_type.get_deps() {
                    return Err(Kind::UnaccountedDependencies);
                }

                state.unify_heap.clone_from(&state.proof_heap);

                let commands = term.get_command_stream();
                let stepper = stream::unify::Stepper::new(stream::unify::Mode::Def, expr, commands);

                TermDef::RunUnify { stepper }
            }
            TermDef::RunUnify { mut stepper } => match stepper.step(state) {
                Some(_) => TermDef::RunUnify { stepper },
                None => TermDef::Done,
            },
            TermDef::Done => TermDef::Done,
        };

        Ok(next)
    }
}

use crate::verifier::store::Store;
use crate::verifier::Heap;

impl<'a> Statement for Verifier<'a> {
    fn term_def(&mut self, idx: u32) -> TResult {
        let term = self.table.get_term(idx).ok_or(Kind::InvalidTerm)?;
        let sort = self
            .table
            .get_sort(term.get_sort())
            .ok_or(Kind::InvalidSort)?;

        if sort.is_pure() {
            return Err(Kind::SortIsPure);
        }

        let binders = term.get_binders();

        self.state.proof_heap.clear();

        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            binder_check(&self.table, *ty, &mut next_bv)?;

            allocate_var(&mut self.state.proof_heap, &mut self.state.store, (i, ty));
        }

        let ret_type = term.get_return_type();

        binder_check(&self.table, ret_type, &mut next_bv)?;

        allocate_var(
            &mut self.state.proof_heap,
            &mut self.state.store,
            (binders.len(), &ret_type),
        );

        self.state.next_bv = next_bv;

        if term.get_sort() != ret_type.get_sort() {
            return Err(Kind::BadReturnType);
        }

        // todo: check if allocation of return var is necessary
        self.state.proof_heap.pop();

        if term.is_definition() {
            let commands = &[];
            stream::proof::Run::run(&mut self.state, &self.table, true, commands)?;

            if self.state.proof_stack.len() != 1 {
                return Err(Kind::StackHasMoreThanOne);
            }

            let expr = self
                .state
                .proof_stack
                .pop()
                .ok_or(Kind::Impossible)?
                .as_expr()
                .ok_or(Kind::InvalidStoreExpr)?;

            let ty = self
                .state
                .store
                .get_type_of_expr(expr)
                .ok_or(Kind::InvalidStoreType)?;

            if !ty.is_compatible_to(&ret_type) {
                return Err(Kind::TypeError);
            }

            if ty.get_deps() != ret_type.get_deps() {
                return Err(Kind::UnaccountedDependencies);
            }

            self.state.unify_heap.clone_from(&self.state.proof_heap);

            let commands = term.get_command_stream();

            stream::unify::Run::run(&mut self.state, commands, stream::unify::Mode::Def, expr)?;
        }

        Ok(())
    }

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult {
        let thm = self.table.get_theorem(idx).ok_or(Kind::InvalidTheorem)?;

        self.state.store.clear();
        self.state.proof_stack.clear();
        self.state.hyp_stack.clear();

        let binders = thm.get_binders();

        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            binder_check(&self.table, *ty, &mut next_bv)?;
            allocate_var(&mut self.state.proof_heap, &mut self.state.store, (i, ty));
        }

        self.state.next_bv = next_bv;

        let commands = &[];
        stream::proof::Run::run(&mut self.state, &self.table, false, commands)?;

        if self.state.proof_stack.len() != 1 {
            return Err(Kind::StackHasMoreThanOne);
        }

        let expr = self.state.proof_stack.pop().ok_or(Kind::Impossible)?;

        let expr = if is_axiom {
            expr.as_expr()
        } else {
            expr.as_proof()
        };

        let expr = expr.ok_or(Kind::InvalidStackType)?;

        let sort = self
            .state
            .store
            .get_type_of_expr(expr)
            .ok_or(Kind::InvalidStoreExpr)?
            .get_sort();

        let sort = self.table.get_sort(sort).ok_or(Kind::InvalidSort)?;

        if !sort.is_provable() {
            return Err(Kind::SortNotProvable);
        }

        self.state.unify_heap.clone_from(&self.state.proof_heap);

        let commands = thm.get_unify_commands();

        stream::unify::Run::run(&mut self.state, commands, stream::unify::Mode::ThmEnd, expr)?;

        Ok(())
    }
}

pub struct Stepper {
    //
}

impl Stepper {
    pub fn step(&mut self, state: &State) -> Option<TResult> {
        //
        Some(Ok(()))
    }
}
