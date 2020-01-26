use crate::error::Kind;
use crate::verifier::context::{store, Context, Ptr, Store};
use crate::verifier::stream;
use crate::verifier::{Sort, State, Table, Term, Theorem, Type};
use crate::TResult;

use crate::opcode;

pub enum FinalizeState {
    Theorem(bool),
    Unfold,
}

pub trait Proof<T>
where
    T: Table,
{
    fn end(&mut self) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, table: &T, sort: u32, current_sort: u32) -> TResult;

    fn term(&mut self, table: &T, idx: u32, current_term: u32, save: bool, def: bool) -> TResult;

    fn theorem(&mut self, table: &T, idx: u32, save: bool) -> TResult;

    fn theorem_start(
        &mut self,
        table: &T,
        idx: u32,
        current_theorem: u32,
        save: bool,
    ) -> TResult<(stream::unify::Stepper, Ptr, bool)>;

    fn theorem_end(&mut self, target: Ptr, save: bool) -> TResult;

    fn hyp(&mut self, table: &T) -> TResult;

    fn conv(&mut self) -> TResult;

    fn refl(&mut self) -> TResult;

    fn symm(&mut self) -> TResult;

    fn cong(&mut self) -> TResult;

    fn unfold_start(&mut self, table: &T) -> TResult<(stream::unify::Stepper, Ptr, Ptr)>;

    fn unfold_end(&mut self, t_ptr: Ptr, e: Ptr) -> TResult;

    fn unfold(&mut self, table: &T) -> TResult;

    fn conv_cut(&mut self) -> TResult;

    fn conv_ref(&mut self, idx: u32) -> TResult;

    fn conv_save(&mut self) -> TResult;

    fn save(&mut self) -> TResult;

    fn execute(
        &mut self,
        table: &T,
        state: &State,
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
            (Dummy, _) => self.dummy(table, command.operand, state.current_sort.into()),
            (Term, _) => self.term(
                table,
                command.operand,
                state.current_term,
                false,
                is_definition,
            ),
            (TermSave, _) => self.term(
                table,
                command.operand,
                state.current_term,
                true,
                is_definition,
            ),
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
            (Save, _) => self.save(),
        }?;

        Ok(false)
    }

    fn step(
        &mut self,
        table: &T,
        state: &State,
        command: opcode::Command<opcode::Proof>,
        is_definition: bool,
    ) -> TResult<Option<FinalizeState>> {
        use crate::opcode::Proof::*;
        match (command.opcode, is_definition) {
            (End, _) => {
                self.end()?;
                return Ok(None);
            }
            (Ref, _) => self.reference(command.operand),
            (Dummy, _) => self.dummy(table, command.operand, state.current_sort.into()),
            (Term, _) => self.term(
                table,
                command.operand,
                state.current_term,
                false,
                is_definition,
            ),
            (TermSave, _) => self.term(
                table,
                command.operand,
                state.current_term,
                true,
                is_definition,
            ),
            (Thm, false) => {
                return Ok(Some(FinalizeState::Theorem(false)));
            }
            (ThmSave, false) => {
                return Ok(Some(FinalizeState::Theorem(true)));
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
                return Ok(Some(FinalizeState::Unfold));
            }
            (ConvCut, _) => self.conv_cut(),
            (ConvRef, _) => self.conv_ref(command.operand),
            (ConvSave, _) => self.conv_save(),
            (Save, _) => self.save(),
        }?;

        //
        Ok(None)
    }
}

impl<T, S: Store> Proof<T> for Context<S>
where
    T: Table<Type = S::Type>,
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

    fn dummy(&mut self, table: &T, sort: u32, current_sort: u32) -> TResult {
        if sort >= current_sort {
            return Err(Kind::SortOutOfRange);
        }

        let s = table.get_sort(sort as u8).ok_or(Kind::InvalidSort)?;

        if s.is_strict() {
            return Err(Kind::SortIsStrict);
        }

        if (self.next_bv >> 56) != 0 {
            return Err(Kind::TooManyBoundVariables);
        }

        let ty = Type::new(sort as u8, self.next_bv, true);

        self.next_bv *= 2;

        let ptr = self.store.alloc_var(ty, self.proof_heap.len() as u16);

        self.proof_stack.push(ptr);
        self.proof_heap.push(ptr);

        Ok(())
    }

    fn term(&mut self, table: &T, idx: u32, current_term: u32, save: bool, def: bool) -> TResult {
        if idx >= current_term {
            return Err(Kind::TermOutOfRange);
        }

        let term = table.get_term(idx).ok_or(Kind::InvalidTerm)?;

        let binders = term.get_binders();
        let nr_args = binders.len();
        let last = self.proof_stack.get_last(nr_args)?;

        let binders = table
            .get_binders(binders)
            .ok_or(Kind::InvalidBinderIndices)?;

        let ptr = self.store.create_term(
            idx,
            last.iter().cloned(),
            binders,
            term.get_return_type(),
            term.get_sort_idx(),
            def,
        )?;

        self.proof_stack.truncate_last(nr_args);

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

        let types = thm.get_binders();
        let nr_args = types.len();
        let last = self.proof_stack.get_last(nr_args)?;

        let types = table.get_binders(types).ok_or(Kind::InvalidBinderIndices)?;

        self.unify_heap.clear();

        let mut g_deps = [0; 256];
        let mut bound: u8 = 0;

        for (i, (&arg, &target_type)) in last.iter().zip(types.iter()).enumerate() {
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
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(nr_args);

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
        current_theorem: u32,
        save: bool,
    ) -> TResult<(stream::unify::Stepper, Ptr, bool)> {
        if idx >= current_theorem {
            return Err(Kind::TheoremOutOfRange);
        }

        let thm = table.get_theorem(idx).ok_or(Kind::InvalidTheorem)?;
        let target = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        let types = thm.get_binders();
        let nr_args = types.len();
        let last = self.proof_stack.get_last(nr_args)?;

        let types = table.get_binders(types).ok_or(Kind::InvalidBinderIndices)?;

        self.unify_heap.clear();

        let mut g_deps = [0; 256];
        let mut bound: u8 = 0;

        for (i, (&arg, &target_type)) in last.iter().zip(types.iter()).enumerate() {
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
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(nr_args);

        let commands = thm.get_unify_commands();

        let stepper = stream::unify::Stepper::new(stream::unify::Mode::Thm, target, commands);

        Ok((stepper, target, save))
    }

    fn theorem_end(&mut self, target: Ptr, save: bool) -> TResult {
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

        let e1: store::Term<_> = self.store.get(e1)?;
        let e2: store::Term<_> = self.store.get(e2)?;

        if e1.id != e2.id {
            return Err(Kind::CongUnifyError);
        }

        for (i, j) in e1.args.iter().zip(e2.args.iter()).rev() {
            self.proof_stack.push(j.to_ptr().to_expr());
            self.proof_stack.push(i.to_ptr().to_co_conv());
        }

        Ok(())
    }

    fn unfold_start(&mut self, table: &T) -> TResult<(stream::unify::Stepper, Ptr, Ptr)> {
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

        let t: store::Term<_> = self.store.get(t_ptr)?;

        let term = table.get_term(*t.id).ok_or(Kind::InvalidTerm)?;

        if !term.is_definition() {
            return Err(Kind::InvalidSort);
        }

        self.unify_heap.clear();
        self.unify_heap.extend(t.args);

        let commands = term.get_command_stream();

        let stepper = stream::unify::Stepper::new(stream::unify::Mode::Def, e, commands);

        Ok((stepper, t_ptr, e))
    }

    fn unfold_end(&mut self, t_ptr: Ptr, e: Ptr) -> TResult {
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

        let t: store::Term<_> = self.store.get(t_ptr)?;

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
        let x: store::Conv = self.store.get(Ptr(idx))?;

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

        let ptr = self.store.alloc_conv(e1.to_expr(), e2.to_expr());
        self.proof_heap.push(ptr);

        Ok(())
    }

    fn save(&mut self) -> TResult {
        let element = self.proof_stack.peek().ok_or(Kind::ProofStackUnderflow)?;

        if element.as_co_conv().is_some() {
            return Err(Kind::CantSaveConvertabilityObligation);
        }

        if element.as_conv().is_some() {
            let e = self.proof_stack.get_last(2)?;

            let l = e[0].to_ptr().to_expr();
            let r = e[1].to_ptr().to_expr();

            let ptr = self.store.alloc_conv(l, r);
            self.proof_heap.push(ptr);

            Ok(())
        } else {
            self.proof_heap.push(*element);
            Ok(())
        }
    }
}

use core::convert::TryInto;

pub trait Run<SS: Store> {
    fn run<T: Table, S>(
        &mut self,
        state: &State,
        table: &T,
        is_definition: bool,
        stream: S,
    ) -> TResult
    where
        T: Table<Type = SS::Type>,
        S: IntoIterator,
        S::Item: TryInto<opcode::Command<opcode::Proof>>;
}

impl<SS: Store> Run<SS> for Context<SS> {
    fn run<T: Table, S>(
        &mut self,
        state: &State,
        table: &T,
        is_definition: bool,
        stream: S,
    ) -> TResult
    where
        T: Table<Type = SS::Type>,
        S: IntoIterator,
        S::Item: TryInto<opcode::Command<opcode::Proof>>,
    {
        for i in stream {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(table, state, command, is_definition)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}

#[derive(Debug)]
pub enum Continue {
    Normal,
    BeforeTheorem {
        idx: u32,
        save: bool,
    },
    Theorem {
        idx: u32,
        save: bool,
    },
    UnifyTheorem {
        stepper: stream::unify::Stepper,
        target: Ptr,
        save: bool,
    },
    ContinueTheorem {
        target: Ptr,
        save: bool,
    },
    BeforeUnfold,
    Unfold,
    UnifyUnfold {
        stepper: stream::unify::Stepper,
        t_ptr: Ptr,
        e: Ptr,
    },
    ContinueUnfold {
        t_ptr: Ptr,
        e: Ptr,
    },
}

#[derive(Debug)]
pub struct Stepper<S> {
    is_definition: bool,
    state: State,
    stream: S,
    idx: usize,
    con: Continue,
}

#[derive(Debug, Copy, Clone)]
pub enum Action {
    Unify(stream::unify::Action),
    UnifyDone,
    UnfoldDone,
    BeforeUnfold,
    UnfoldApplied,
    TheoremDone,
    BeforeTheorem(u32),
    TheoremApplied,
    Cmd(usize, opcode::Command<opcode::Proof>),
}

impl<S> Stepper<S>
where
    S: Iterator<Item = opcode::Command<opcode::Proof>>,
{
    pub fn new(is_definition: bool, state: State, stream: S) -> Stepper<S> {
        Stepper {
            is_definition,
            state,
            stream,
            idx: 0,
            con: Continue::Normal,
        }
    }

    pub fn take_stream(self) -> S {
        self.stream
    }

    pub fn run<SS: Store, T: Table<Type = SS::Type>>(
        &mut self,
        context: &mut Context<SS>,
        table: &T,
    ) -> TResult<()> {
        while self.step(context, table)?.is_some() {}

        Ok(())
    }

    pub fn step<SS: Store, T: Table<Type = SS::Type>>(
        &mut self,
        context: &mut Context<SS>,
        table: &T,
    ) -> TResult<Option<Action>> {
        let (next_state, ret) = match &mut self.con {
            Continue::Normal => {
                if let Some(command) = self.stream.next() {
                    let idx = self.idx;
                    self.idx += 1;

                    let next_state =
                        match context.step(table, &self.state, command, self.is_definition)? {
                            Some(FinalizeState::Theorem(save)) => Continue::BeforeTheorem {
                                idx: command.operand,
                                save,
                            },
                            Some(FinalizeState::Unfold) => Continue::BeforeUnfold,
                            None => Continue::Normal,
                        };

                    (Some(next_state), Ok(Some(Action::Cmd(idx, command))))
                } else {
                    (None, Ok(None))
                }
            }
            Continue::BeforeTheorem { ref idx, ref save } => (
                Some(Continue::Theorem {
                    idx: *idx,
                    save: *save,
                }),
                Ok(Some(Action::BeforeTheorem(*idx))),
            ),
            Continue::Theorem { idx, save } => {
                let (x, a, b) =
                    context.theorem_start(table, *idx, self.state.current_theorem, *save)?;
                (
                    Some(Continue::UnifyTheorem {
                        stepper: x,
                        target: a,
                        save: b,
                    }),
                    Ok(Some(Action::TheoremApplied)),
                )
            }

            Continue::BeforeUnfold => (Some(Continue::Unfold), Ok(Some(Action::BeforeUnfold))),
            Continue::Unfold => {
                let (x, a, b) = context.unfold_start(table)?;
                (
                    Some(Continue::UnifyUnfold {
                        stepper: x,
                        t_ptr: a,
                        e: b,
                    }),
                    Ok(Some(Action::UnfoldApplied)),
                )
            }
            Continue::UnifyUnfold {
                ref mut stepper,
                ref t_ptr,
                ref e,
            } => match stepper.step(context, table)? {
                Some(x) => (None, Ok(Some(Action::Unify(x)))),
                None => (
                    Some(Continue::ContinueUnfold {
                        t_ptr: *t_ptr,
                        e: *e,
                    }),
                    Ok(Some(Action::UnifyDone)),
                ),
            },
            Continue::ContinueUnfold { t_ptr, e } => {
                Proof::<T>::unfold_end(context, *t_ptr, *e)?;
                (Some(Continue::Normal), Ok(Some(Action::UnfoldDone)))
            }
            Continue::UnifyTheorem {
                ref mut stepper,
                ref target,
                ref save,
            } => match stepper.step(context, table)? {
                Some(x) => (None, Ok(Some(Action::Unify(x)))),
                None => (
                    Some(Continue::ContinueTheorem {
                        target: *target,
                        save: *save,
                    }),
                    Ok(Some(Action::UnifyDone)),
                ),
            },
            Continue::ContinueTheorem { target, save } => {
                Proof::<T>::theorem_end(context, *target, *save)?;
                (Some(Continue::Normal), Ok(Some(Action::TheoremDone)))
            }
        };

        if let Some(x) = next_state {
            self.con = x;
        }

        ret
    }
}
