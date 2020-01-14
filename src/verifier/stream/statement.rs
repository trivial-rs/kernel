use crate::error::Kind;
use crate::verifier::store::Store;
use crate::verifier::stream;
use crate::verifier::Heap;
use crate::verifier::State;
use crate::verifier::StoreElement;
use crate::verifier::TableLike;
use crate::verifier::Term;
use crate::verifier::Type;
use crate::TResult;

use core::ops::Range;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Opcode {
    End,
    Sort,
    TermDef,
    Axiom,
    Thm,
}

pub trait StatementStream: Iterator
where
    <Self as Iterator>::Item: TryInto<Opcode>,
{
    type AsProof: Iterator<Item = u32> + std::fmt::Debug;

    fn as_proof_stream(&self) -> Self::AsProof;
}

fn allocate_var(proof_heap: &mut Heap, store: &mut Store, x: (usize, &Type)) {
    let var = StoreElement::Var {
        ty: *x.1,
        var: x.0 as u16,
    };

    let ptr = store.push(var);
    proof_heap.push(ptr);
}

fn binder_check<T: TableLike>(table: &T, ty: Type, bv: &mut u64) -> TResult {
    let sort = table.get_sort(ty.get_sort_idx()).ok_or(Kind::InvalidSort)?;
    let deps = ty.get_deps();

    if ty.is_bound() {
        if sort.is_strict() {
            return Err(Kind::SortIsStrict);
        }

        if deps != *bv {
            return Err(Kind::BindDep);
        }

        *bv *= 2;
    } else if (deps & !(*bv - 1)) != 0 {
        return Err(Kind::BindDep);
    }

    Ok(())
}

pub trait Statement {
    fn term_def(&mut self, idx: u32) -> TResult;

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult;
}

#[derive(Debug)]
pub enum TermDef<S>
where
    S: Iterator<Item = u32>,
{
    Start {
        idx: u32,
        stream: S,
    },
    RunProof {
        stepper: stream::proof::Stepper<S>,
        ret_type: Type,
        commands: Range<usize>,
    },
    ProofDone {
        ret_type: Type,
        commands: Range<usize>,
    },
    RunUnify {
        stepper: stream::unify::Stepper,
    },
    Done,
}

use std::convert::TryInto;

impl<S> TermDef<S>
where
    S: Iterator<Item = u32>,
{
    pub fn new(idx: u32, stream: S) -> TermDef<S> {
        TermDef::Start { idx, stream }
    }

    pub fn is_done(&self) -> bool {
        match self {
            TermDef::Done => true,
            _ => false,
        }
    }

    pub fn step<T: TableLike>(&mut self, state: &mut State, table: &T) -> TResult {
        let old = std::mem::replace(self, Self::Done);

        let next = match old {
            TermDef::Start { idx, stream } => {
                let term = table.get_term(idx).ok_or(Kind::InvalidTerm)?;
                let sort = table
                    .get_sort(term.get_sort_idx())
                    .ok_or(Kind::InvalidSort)?;

                if sort.is_pure() {
                    return Err(Kind::SortIsPure);
                }

                let binders = term.get_binders();
                let binders = table
                    .get_binders(binders)
                    .ok_or(Kind::InvalidBinderIndices)?;

                state.store.clear();
                state.proof_stack.clear();
                state.proof_heap.clear();
                state.unify_stack.clear();
                state.unify_heap.clear();
                state.hyp_stack.clear();

                let mut next_bv = 1;

                for (i, ty) in binders.iter().enumerate() {
                    binder_check(table, *ty, &mut next_bv)?;

                    allocate_var(&mut state.proof_heap, &mut state.store, (i, ty));
                }

                let ret_type = term.get_return_type();

                binder_check(table, ret_type, &mut next_bv)?;

                state.next_bv = next_bv;

                if term.get_sort_idx() != ret_type.get_sort_idx() {
                    return Err(Kind::BadReturnType);
                }

                if !term.is_definition() {
                    TermDef::Done
                } else {
                    let stepper = stream::proof::Stepper::new(true, stream);

                    let commands = term.get_command_stream();

                    TermDef::RunProof {
                        stepper,
                        ret_type,
                        commands,
                    }
                }
            }
            TermDef::RunProof {
                mut stepper,
                ret_type,
                commands,
            } => match stepper.step(state, table) {
                Some(Ok(())) => TermDef::RunProof {
                    stepper,
                    ret_type,
                    commands,
                },
                Some(Err(x)) => {
                    return Err(x);
                }
                None => TermDef::ProofDone { ret_type, commands },
            },
            TermDef::ProofDone { ret_type, commands } => {
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

                if !ty.is_compatible_to(ret_type) {
                    return Err(Kind::TypeError);
                }

                if ty.get_deps() != ret_type.get_deps() {
                    return Err(Kind::UnaccountedDependencies);
                }

                state.unify_heap.clone_from(&state.proof_heap);

                let stepper = stream::unify::Stepper::new(stream::unify::Mode::Def, expr, commands);

                TermDef::RunUnify { stepper }
            }
            TermDef::RunUnify { mut stepper } => match stepper.step(state, table) {
                Some(Ok(())) => TermDef::RunUnify { stepper },
                Some(Err(x)) => {
                    return Err(x);
                }
                None => TermDef::Done,
            },
            TermDef::Done => TermDef::Done,
        };

        std::mem::replace(self, next);

        Ok(())
    }
}

#[derive(Debug)]
pub enum AxiomThm<S>
where
    S: Iterator<Item = u32>,
{
    Start {
        idx: u32,
        is_axiom: bool,
        stream: S,
    },
    RunProof {
        stepper: stream::proof::Stepper<S>,
        is_axiom: bool,
        commands: Range<usize>,
    },
    ProofDone {
        is_axiom: bool,
        commands: Range<usize>,
    },
    RunUnify {
        stepper: stream::unify::Stepper,
    },
    Done,
}

impl<S> AxiomThm<S>
where
    S: Iterator<Item = u32>,
{
    pub fn new(idx: u32, stream: S, is_axiom: bool) -> AxiomThm<S> {
        AxiomThm::Start {
            idx,
            stream,
            is_axiom,
        }
    }

    pub fn is_done(&self) -> bool {
        match self {
            AxiomThm::Done => true,
            _ => false,
        }
    }

    pub fn step<T: TableLike>(&mut self, state: &mut State, table: &T) -> TResult {
        let old = std::mem::replace(self, Self::Done);

        let next = match old {
            AxiomThm::Start {
                idx,
                stream,
                is_axiom,
            } => {
                let thm = table.get_theorem(idx).ok_or(Kind::InvalidTheorem)?;

                state.store.clear();
                state.proof_stack.clear();
                state.proof_heap.clear();
                state.unify_stack.clear();
                state.unify_heap.clear();
                state.hyp_stack.clear();

                let binders = thm.get_binders();
                let binders = table
                    .get_binders(binders)
                    .ok_or(Kind::InvalidBinderIndices)?;

                let mut next_bv = 1;

                for (i, ty) in binders.iter().enumerate() {
                    binder_check(table, *ty, &mut next_bv)?;
                    allocate_var(&mut state.proof_heap, &mut state.store, (i, ty));
                }

                state.next_bv = next_bv;

                let stepper = stream::proof::Stepper::new(false, stream);

                let commands = thm.get_unify_commands();

                AxiomThm::RunProof {
                    stepper,
                    commands,
                    is_axiom,
                }
            }
            AxiomThm::RunProof {
                mut stepper,
                commands,
                is_axiom,
            } => match stepper.step(state, table) {
                Some(Ok(())) => AxiomThm::RunProof {
                    stepper,
                    commands,
                    is_axiom,
                },
                Some(Err(x)) => {
                    return Err(x);
                }
                None => AxiomThm::ProofDone { commands, is_axiom },
            },
            AxiomThm::ProofDone { commands, is_axiom } => {
                if state.proof_stack.len() != 1 {
                    return Err(Kind::StackHasMoreThanOne);
                }

                let expr = state.proof_stack.pop().ok_or(Kind::Impossible)?;

                let expr = if is_axiom {
                    expr.as_expr()
                } else {
                    expr.as_proof()
                };

                let expr = expr.ok_or(Kind::InvalidStackType)?;

                let sort = state
                    .store
                    .get_type_of_expr(expr)
                    .ok_or(Kind::InvalidStoreExpr)?
                    .get_sort_idx();

                let sort = table.get_sort(sort).ok_or(Kind::InvalidSort)?;

                if !sort.is_provable() {
                    return Err(Kind::SortNotProvable);
                }

                state.unify_heap.clone_from(&state.proof_heap);

                let stepper =
                    stream::unify::Stepper::new(stream::unify::Mode::ThmEnd, expr, commands);

                AxiomThm::RunUnify { stepper }
            }
            AxiomThm::RunUnify { mut stepper } => match stepper.step(state, table) {
                Some(Ok(())) => AxiomThm::RunUnify { stepper },
                Some(Err(x)) => {
                    return Err(x);
                }
                None => AxiomThm::Done,
            },
            AxiomThm::Done => AxiomThm::Done,
        };

        std::mem::replace(self, next);

        Ok(())
    }
}

#[derive(Debug)]
enum StepState<S>
where
    S: Iterator<Item = u32>,
{
    Normal,
    TermDef(TermDef<S>),
    AxiomThm(AxiomThm<S>),
}

#[derive(Debug)]
pub struct Stepper<S>
where
    S: StatementStream + Iterator,
    <S as Iterator>::Item: TryInto<Opcode>,
{
    stream: S,
    state: StepState<S::AsProof>,
}

impl<S> Stepper<S>
where
    S: StatementStream + Iterator,
    <S as Iterator>::Item: TryInto<Opcode>,
{
    pub fn new(stream: S) -> Stepper<S> {
        Stepper {
            stream,
            state: StepState::Normal,
        }
    }

    pub fn step<T: TableLike>(&mut self, state: &mut State, table: &T) -> Option<TResult> {
        let mut old = std::mem::replace(&mut self.state, StepState::Normal);

        match old {
            StepState::Normal => self.normal(state),
            StepState::TermDef(ref mut td) => {
                if td.is_done() {
                    std::mem::replace(&mut self.state, StepState::Normal);
                    state.increment_current_term();
                    Some(Ok(()))
                } else {
                    let ret = td.step(state, table);
                    std::mem::replace(&mut self.state, old);
                    Some(ret)
                }
            }
            StepState::AxiomThm(ref mut at) => {
                if at.is_done() {
                    std::mem::replace(&mut self.state, StepState::Normal);
                    state.increment_current_theorem();
                    Some(Ok(()))
                } else {
                    let ret = at.step(state, table);
                    std::mem::replace(&mut self.state, old);
                    Some(ret)
                }
            }
        }
    }

    fn normal(&mut self, state: &mut State) -> Option<TResult> {
        if let Some(x) = self.stream.next() {
            let x = x.try_into().ok()?;

            match x {
                Opcode::End => {
                    //
                }
                Opcode::Sort => {
                    //
                }
                Opcode::TermDef => {
                    let td = TermDef::new(state.get_current_term(), self.stream.as_proof_stream());

                    self.state = StepState::TermDef(td);
                }
                Opcode::Axiom => {
                    let at = AxiomThm::new(
                        state.get_current_theorem(),
                        self.stream.as_proof_stream(),
                        true,
                    );
                    self.state = StepState::AxiomThm(at);
                }
                Opcode::Thm => {
                    let at = AxiomThm::new(
                        state.get_current_theorem(),
                        self.stream.as_proof_stream(),
                        false,
                    );
                    self.state = StepState::AxiomThm(at);
                }
            }

            Some(Ok(()))
        } else {
            None
        }
    }
}
