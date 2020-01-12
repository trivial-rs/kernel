use crate::error::Kind;
use crate::verifier::store::StoreElement;
use crate::verifier::store::StoreTerm;
use crate::verifier::store::Type;
use crate::verifier::stream;
use crate::verifier::{State, Table, TableLike, Term};
use crate::TResult;

use crate::opcode;
use crate::verifier::store::StorePointer;

pub enum FinalizeState {
    Theorem(StorePointer, bool),
    Unfold(StorePointer, StorePointer),
}

pub trait Proof<'a, T>
where
    T: TableLike,
{
    fn end(&mut self) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, table: &T, sort: u32) -> TResult;

    fn term(&mut self, table: &T, idx: u32, save: bool, def: bool) -> TResult;

    fn theorem(&mut self, table: &T, idx: u32, save: bool) -> TResult;

    fn theorem_start(
        &mut self,
        table: &T,
        idx: u32,
        save: bool,
    ) -> TResult<(stream::unify::Stepper, FinalizeState)>;

    fn theorem_end(&mut self, target: StorePointer, save: bool) -> TResult;

    fn hyp(&mut self, table: &T) -> TResult;

    fn conv(&mut self) -> TResult;

    fn refl(&mut self) -> TResult;

    fn symm(&mut self) -> TResult;

    fn cong(&mut self) -> TResult;

    fn unfold_start(&mut self, table: &'a T) -> TResult<(stream::unify::Stepper, FinalizeState)>;

    fn unfold_end(&mut self, t_ptr: StorePointer, e: StorePointer) -> TResult;

    fn unfold(&mut self, table: &T) -> TResult;

    fn conv_cut(&mut self) -> TResult;

    fn conv_ref(&mut self, idx: u32) -> TResult;

    fn conv_save(&mut self) -> TResult;

    fn execute(
        &mut self,
        table: &T,
        command: opcode::Command<opcode::Proof>,
        is_definition: bool,
    ) -> TResult<bool> {
        use crate::opcode::Proof::*;
        match (command.opcode, is_definition) {
            (End, _) => {
                self.end()?;
                return Ok(true);
            }
            (Ref, _) => self.reference(command.operand),
            (Dummy, _) => self.dummy(table, command.operand),
            (Term, _) => self.term(table, command.operand, false, is_definition),
            (TermSave, _) => self.term(table, command.operand, true, is_definition),
            (Thm, false) => self.theorem(table, command.operand, false),
            (ThmSave, false) => self.theorem(table, command.operand, true),
            (Thm, true) => Err(Kind::InvalidOpcodeInDef),
            (ThmSave, true) => Err(Kind::InvalidOpcodeInDef),
            (Hyp, false) => self.hyp(table),
            (Hyp, true) => Err(Kind::InvalidOpcodeInDef),
            (Conv, _) => self.conv(),
            (Refl, _) => self.refl(),
            (Symm, _) => self.symm(),
            (Cong, _) => self.cong(),
            (Unfold, _) => self.unfold(table),
            (ConvCut, _) => self.conv_cut(),
            (ConvRef, _) => self.conv_ref(command.operand),
            (ConvSave, _) => self.conv_save(),
        }?;

        Ok(false)
    }

    fn step(
        &mut self,
        table: &'a T,
        command: opcode::Command<opcode::Proof>,
        is_definition: bool,
    ) -> TResult<Option<(stream::unify::Stepper, FinalizeState)>> {
        use crate::opcode::Proof::*;
        match (command.opcode, is_definition) {
            (End, _) => {
                self.end()?;
                return Ok(None);
            }
            (Ref, _) => self.reference(command.operand),
            (Dummy, _) => self.dummy(table, command.operand),
            (Term, _) => self.term(table, command.operand, false, is_definition),
            (TermSave, _) => self.term(table, command.operand, true, is_definition),
            (Thm, false) => {
                let a = self.theorem_start(table, command.operand, false)?;
                return Ok(Some(a));
            }
            (ThmSave, false) => {
                let a = self.theorem_start(table, command.operand, true)?;
                return Ok(Some(a));
            }
            (Thm, true) => Err(Kind::InvalidOpcodeInDef),
            (ThmSave, true) => Err(Kind::InvalidOpcodeInDef),
            (Hyp, false) => self.hyp(table),
            (Hyp, true) => Err(Kind::InvalidOpcodeInDef),
            (Conv, _) => self.conv(),
            (Refl, _) => self.refl(),
            (Symm, _) => self.symm(),
            (Cong, _) => self.cong(),
            (Unfold, _) => {
                let a = self.unfold_start(table)?;
                return Ok(Some(a));
            }
            (ConvCut, _) => self.conv_cut(),
            (ConvRef, _) => self.conv_ref(command.operand),
            (ConvSave, _) => self.conv_save(),
        }?;

        //
        Ok(None)
    }
}

impl<'a, T> Proof<'a, T> for State
where
    T: TableLike,
{
    fn end(&mut self) -> TResult {
        // todo: make this check the stack?
        Ok(())
    }

    fn reference(&mut self, idx: u32) -> TResult {
        let i = self.proof_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;

        self.proof_stack.push(i);

        Ok(())
    }

    fn dummy(&mut self, table: &T, sort: u32) -> TResult {
        let s = table.get_sort(sort as u8).ok_or(Kind::InvalidSort)?;

        if s.is_strict() {
            return Err(Kind::SortIsStrict);
        }

        if (self.next_bv >> 56) != 0 {
            return Err(Kind::TooManyBoundVariables);
        }

        let ty = Type::new(sort as u8, self.next_bv, true);

        self.next_bv *= 2;

        let var = StoreElement::Var {
            ty,
            var: self.proof_heap.len() as u16,
        };

        let ptr = self.store.push(var);

        self.proof_stack.push(ptr);
        self.proof_heap.push(ptr);

        Ok(())
    }

    fn term(&mut self, table: &T, idx: u32, save: bool, def: bool) -> TResult {
        let term = table.get_term(idx).ok_or(Kind::InvalidTerm)?;
        let last = self.proof_stack.get_last(term.nr_args())?;

        let binders = term.get_binders();
        let binders = table
            .get_binders(binders)
            .ok_or(Kind::InvalidBinderIndices)?;

        let ptr = self.store.create_term(
            idx,
            last,
            binders,
            term.get_return_type(),
            term.get_sort_idx(),
            def,
        )?;

        self.proof_stack.truncate_last(term.nr_args());

        self.proof_stack.push(ptr);

        if save {
            self.proof_heap.push(ptr);
        }

        Ok(())
    }

    fn theorem(&mut self, table: &T, idx: u32, save: bool) -> TResult {
        let thm = table.get_theorem(idx).ok_or(Kind::InvalidTheorem)?;
        let target = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;
        let last = self.proof_stack.get_last(thm.get_nr_args())?;

        let types = thm.get_binders();
        let types = table.get_binders(types).ok_or(Kind::InvalidBinderIndices)?;

        self.unify_heap.clear();

        let mut g_deps = [0; 256];
        let mut bound: u8 = 0;
        let mut i = 0;

        for (&arg, &target_type) in last.iter().zip(types.iter()) {
            let arg = arg.as_expr().ok_or(Kind::InvalidStoreExpr)?;

            let ty = self
                .store
                .get_type_of_expr(arg)
                .ok_or(Kind::InvalidStoreExpr)?;

            let deps = ty.get_deps();

            if target_type.is_bound() {
                *g_deps
                    .get_mut(bound as usize)
                    .ok_or(Kind::DependencyOverflow)? = deps;

                bound += 1;

                for &i in last.get(..i).ok_or(Kind::DependencyOverflow)? {
                    let i = i.as_expr().ok_or(Kind::InvalidStoreExpr)?;

                    let d = self
                        .store
                        .get_type_of_expr(i)
                        .ok_or(Kind::InvalidStoreExpr)?;

                    if d.depends_on_full(deps) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            } else {
                for (i, &j) in g_deps
                    .get(..(bound as usize))
                    .ok_or(Kind::DependencyOverflow)?
                    .iter()
                    .enumerate()
                {
                    if !(target_type.depends_on(i as u8) || ((j & deps) == 0)) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            }

            i += 1;
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(thm.get_nr_args());

        let commands = thm.get_unify_commands();

        stream::unify::Run::run(self, commands, table, stream::unify::Mode::Thm, target)?;

        let proof = target.to_proof();

        self.proof_stack.push(proof);

        if save {
            self.proof_heap.push(proof);
        }

        Ok(())
    }

    fn theorem_start(
        &mut self,
        table: &T,
        idx: u32,
        save: bool,
    ) -> TResult<(stream::unify::Stepper, FinalizeState)> {
        let thm = table.get_theorem(idx).ok_or(Kind::InvalidTheorem)?;
        let target = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;
        let last = self.proof_stack.get_last(thm.get_nr_args())?;

        let types = thm.get_binders();
        let types = table.get_binders(types).ok_or(Kind::InvalidBinderIndices)?;

        self.unify_heap.clear();

        let mut g_deps = [0; 256];
        let mut bound: u8 = 0;
        let mut i = 0;

        for (&arg, &target_type) in last.iter().zip(types.iter()) {
            let arg = arg.as_expr().ok_or(Kind::InvalidStoreExpr)?;

            let ty = self
                .store
                .get_type_of_expr(arg)
                .ok_or(Kind::InvalidStoreExpr)?;

            let deps = ty.get_deps();

            if target_type.is_bound() {
                *g_deps
                    .get_mut(bound as usize)
                    .ok_or(Kind::DependencyOverflow)? = deps;

                bound += 1;

                for &i in last.get(..i).ok_or(Kind::DependencyOverflow)? {
                    let i = i.as_expr().ok_or(Kind::InvalidStoreExpr)?;

                    let d = self
                        .store
                        .get_type_of_expr(i)
                        .ok_or(Kind::InvalidStoreExpr)?;

                    if d.depends_on_full(deps) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            } else {
                for (i, &j) in g_deps
                    .get(..(bound as usize))
                    .ok_or(Kind::DependencyOverflow)?
                    .iter()
                    .enumerate()
                {
                    if !(target_type.depends_on(i as u8) || ((j & deps) == 0)) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            }

            i += 1;
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(thm.get_nr_args());

        let commands = thm.get_unify_commands();

        let stepper = stream::unify::Stepper::new(stream::unify::Mode::Thm, target, commands);

        Ok((stepper, FinalizeState::Theorem(target, save)))
    }

    fn theorem_end(&mut self, target: StorePointer, save: bool) -> TResult {
        let proof = target.to_proof();

        self.proof_stack.push(proof);

        if save {
            self.proof_heap.push(proof);
        }

        Ok(())
    }

    fn hyp(&mut self, table: &T) -> TResult {
        let e = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;
        let ty = self
            .store
            .get_type_of_expr(e)
            .ok_or(Kind::InvalidStoreExpr)?;

        let sort = table.get_sort(ty.get_sort_idx()).ok_or(Kind::InvalidSort)?;

        if !sort.is_provable() {
            return Err(Kind::SortNotProvable);
        }

        self.hyp_stack.push(e.to_expr());
        self.proof_heap.push(e.to_proof());

        Ok(())
    }

    fn conv(&mut self) -> TResult {
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_proof()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        self.proof_stack.push(e1.to_proof());
        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_co_conv());

        Ok(())
    }

    fn refl(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        if e1 != e2 {
            return Err(Kind::UnifyRefFailure);
        }

        Ok(())
    }

    fn symm(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        self.proof_stack.push(e1.to_expr());
        self.proof_stack.push(e2.to_co_conv());

        Ok(())
    }

    fn cong(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e1: StoreTerm = self.store.get(e1)?;
        let e2: StoreTerm = self.store.get(e2)?;

        if e1.id != e2.id {
            return Err(Kind::CongUnifyError);
        }

        for (i, j) in e1.args.iter().zip(e2.args.iter()).rev() {
            self.proof_stack.push(j.to_ptr().to_expr());
            self.proof_stack.push(i.to_ptr().to_co_conv());
        }

        Ok(())
    }

    fn unfold_start(&mut self, table: &'a T) -> TResult<(stream::unify::Stepper, FinalizeState)> {
        let e = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t_ptr = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t: StoreTerm = self.store.get(t_ptr)?;

        let term = table.get_term(*t.id).ok_or(Kind::InvalidTerm)?;

        if !term.is_definition() {
            return Err(Kind::InvalidSort);
        }

        self.unify_heap.clear();
        self.unify_heap.extend(t.args);

        let commands = term.get_command_stream();

        let stepper = stream::unify::Stepper::new(stream::unify::Mode::Def, e, commands);

        Ok((stepper, FinalizeState::Unfold(t_ptr, e)))
    }

    fn unfold_end(&mut self, t_ptr: StorePointer, e: StorePointer) -> TResult {
        let t_prime = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreType)?;

        if t_ptr != t_prime {
            return Err(Kind::UnifyTermFailure);
        }

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e.to_co_conv());

        Ok(())
    }

    fn unfold(&mut self, table: &T) -> TResult {
        let e = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t_ptr = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t: StoreTerm = self.store.get(t_ptr)?;

        let term = table.get_term(*t.id).ok_or(Kind::InvalidTerm)?;

        if !term.is_definition() {
            return Err(Kind::InvalidSort);
        }

        self.unify_heap.clear();
        self.unify_heap.extend(t.args);

        let commands = term.get_command_stream();

        stream::unify::Run::run(self, commands, table, stream::unify::Mode::Def, e)?;

        let t_prime = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreType)?;

        if t_ptr != t_prime {
            return Err(Kind::UnifyTermFailure);
        }

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e.to_co_conv());

        Ok(())
    }

    fn conv_cut(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_conv());

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_co_conv());

        Ok(())
    }

    fn conv_ref(&mut self, idx: u32) -> TResult {
        use crate::verifier::store::StoreConv;

        let x: StoreConv = self.store.get(StorePointer(idx))?;

        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        if x.e1.to_ptr() != e1 || x.e2.to_ptr() != e2 {
            return Err(Kind::UnifyRefFailure);
        }

        Ok(())
    }

    fn conv_save(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_conv()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        let conv = StoreElement::Conv {
            e1: e1.to_expr(),
            e2: e2.to_expr(),
        };

        let ptr = self.store.push(conv);
        self.proof_heap.push(ptr);

        Ok(())
    }
}

use std::convert::TryInto;

pub trait Run {
    fn run<T>(&mut self, table: &Table, is_definition: bool, stream: T) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<opcode::Command<opcode::Proof>>;
}

impl Run for State {
    fn run<T>(&mut self, table: &Table, is_definition: bool, stream: T) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<opcode::Command<opcode::Proof>>,
    {
        for i in stream {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(table, command, is_definition)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}

#[derive(Debug)]
pub enum Continue {
    Normal,
    UnifyTheorem {
        stepper: stream::unify::Stepper,
        target: StorePointer,
        save: bool,
    },
    ContinueTheorem {
        target: StorePointer,
        save: bool,
    },
    UnifyUnfold {
        stepper: stream::unify::Stepper,
        t_ptr: StorePointer,
        e: StorePointer,
    },
    ContinueUnfold {
        t_ptr: StorePointer,
        e: StorePointer,
    },
}

#[derive(Debug)]
pub struct Stepper<S> {
    // we can't own &mut State, because of ownership issues
    is_definition: bool,
    stream: S,
    con: Continue,
}

impl<S> Stepper<S>
where
    S: Iterator<Item = u32>,
{
    pub fn new(is_definition: bool, stream: S) -> Stepper<S> {
        Stepper {
            is_definition,
            stream,
            con: Continue::Normal,
        }
    }

    pub fn step<T: TableLike>(&mut self, state: &mut State, table: &T) -> Option<TResult> {
        let (next, ret) = match &mut self.con {
            Continue::Normal => {
                if let Some(el) = self.stream.next() {
                    //println!("cmnd: {}", el);
                    let el = table.get_proof_command(el);

                    //println!("Proof step: {:?}", el);

                    let (next_state, ret) = match el {
                        Some(i) => {
                            let command = i.try_into().ok()?;
                            //println!("{:?}", command);

                            let k = match state.step(table, command, self.is_definition) {
                                Ok(x) => {
                                    let next_state = match x {
                                        Some((x, FinalizeState::Theorem(a, b))) => {
                                            Continue::UnifyTheorem {
                                                stepper: x,
                                                target: a,
                                                save: b,
                                            }
                                            //
                                        }
                                        Some((x, FinalizeState::Unfold(a, b))) => {
                                            Continue::UnifyUnfold {
                                                stepper: x,
                                                t_ptr: a,
                                                e: b,
                                            }
                                            //
                                        }
                                        None => Continue::Normal,
                                    };

                                    Some(next_state)
                                }
                                Err(x) => {
                                    return Some(Err(x));
                                }
                            };

                            (k, Some(Ok(())))
                        }
                        None => (None, None),
                    };

                    (next_state, ret)
                } else {
                    (None, None)
                }
            }
            Continue::UnifyUnfold {
                ref mut stepper,
                ref t_ptr,
                ref e,
            } => {
                let (next_state, ret) = match stepper.step(state, table) {
                    Some(x) => (None, Some(x)),
                    None => (
                        Some(Continue::ContinueUnfold {
                            t_ptr: *t_ptr,
                            e: *e,
                        }),
                        None,
                    ),
                };

                (next_state, ret)
            }
            Continue::ContinueUnfold { t_ptr, e } => {
                let a = Proof::<T>::unfold_end(state, *t_ptr, *e);

                (Some(Continue::Normal), Some(a))
            }
            Continue::UnifyTheorem {
                ref mut stepper,
                ref target,
                ref save,
            } => {
                let (next_state, ret) = match stepper.step(state, table) {
                    Some(x) => (None, Some(x)),
                    None => (
                        Some(Continue::ContinueTheorem {
                            target: *target,
                            save: *save,
                        }),
                        None,
                    ),
                };
                (next_state, ret)
            }
            Continue::ContinueTheorem { target, save } => {
                let a = Proof::<T>::theorem_end(state, *target, *save);
                (Some(Continue::Normal), Some(a))
            }
        };

        if let Some(x) = next {
            self.con = x;
        }

        ret
    }
}
