use crate::error::Kind;
use crate::verifier::state::Heap;
use crate::verifier::state::State;
use crate::verifier::state::Store;
use crate::verifier::stream;
use crate::verifier::{Sort, Table, Term, Theorem, Type};
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

use crate::opcode;

pub trait StatementStream: Iterator
where
    <Self as Iterator>::Item: TryInto<Opcode>,
{
    type ProofStream: Iterator<Item = opcode::Command<opcode::Proof>>;

    fn take_proof_stream(&mut self) -> Self::ProofStream;

    fn put_proof_stream(&mut self, proofs: Self::ProofStream);
}

pub trait Statement {
    fn term_def(&mut self, idx: u32) -> TResult;

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult;
}

#[derive(Debug)]
pub enum TermDef<S, Ty> {
    Start {
        idx: u32,
        stream: S,
    },
    RunProof {
        stepper: stream::proof::Stepper<S>,
        ret_type: Ty,
        nr_args: usize,
        commands: Range<usize>,
    },
    ProofDone {
        stream: S,
        ret_type: Ty,
        commands: Range<usize>,
        nr_args: usize,
    },
    RunUnify {
        stream: S,
        stepper: stream::unify::Stepper,
    },
    Done {
        stream: S,
    },
    Dummy,
}

use core::convert::TryInto;

#[derive(Debug)]
pub enum TermDefAction {
    Done,
    StartProof,
    Proof(stream::proof::Action),
    ProofDone,
    StartUnify,
    Unify(stream::unify::Action),
    UnifyDone,
}

impl<S, Ty> TermDef<S, Ty>
where
    S: Iterator<Item = opcode::Command<opcode::Proof>>,
    Ty: Type,
{
    pub fn new(idx: u32, stream: S) -> TermDef<S, Ty> {
        TermDef::Start { idx, stream }
    }

    pub fn take_stream_if_done(self) -> Option<S> {
        match self {
            TermDef::Done { stream } => Some(stream),
            _ => None,
        }
    }

    pub fn is_done(&self) -> bool {
        match self {
            TermDef::Done { .. } => true,
            _ => false,
        }
    }

    pub fn step<SS: Store<Type = Ty>, T: Table<Type = SS::Type>>(
        &mut self,
        state: &mut State<SS>,
        table: &T,
    ) -> TResult<TermDefAction> {
        let old = core::mem::replace(self, Self::Dummy);

        let (next_state, ret_val) = match old {
            TermDef::Start { idx, stream } => {
                let term = table.get_term(idx).ok_or(Kind::InvalidTerm)?;

                let sort_idx = term.get_sort_idx();
                let current_sort = state.get_current_sort();

                if sort_idx >= current_sort {
                    return Err(Kind::SortOutOfRange);
                }

                let sort = table.get_sort(sort_idx).ok_or(Kind::InvalidSort)?;

                if sort.is_pure() {
                    return Err(Kind::SortIsPure);
                }

                let binders = term.get_binders();
                let nr_args = binders.len();
                let binders = table
                    .get_binders(binders)
                    .ok_or(Kind::InvalidBinderIndices)?;

                state.store.clear();
                state.proof_stack.clear();
                state.proof_heap.clear();
                state.unify_stack.clear();
                state.unify_heap.clear();
                state.hyp_stack.clear();

                state.allocate_binders(table, binders)?;

                let mut next_bv = state.next_bv;
                let ret_type = term.get_return_type();

                State::<SS>::binder_check(table, ret_type, current_sort, &mut next_bv)?;

                state.next_bv = next_bv;

                if term.get_sort_idx() != ret_type.get_sort_idx() {
                    return Err(Kind::BadReturnType);
                }

                if !term.is_definition() {
                    (TermDef::Done { stream }, TermDefAction::Done)
                } else {
                    let stepper = stream::proof::Stepper::new(true, stream);

                    let commands = term.get_command_stream();

                    (
                        TermDef::RunProof {
                            stepper,
                            ret_type: *ret_type,
                            nr_args,
                            commands,
                        },
                        TermDefAction::StartProof,
                    )
                }
            }
            TermDef::RunProof {
                mut stepper,
                ret_type,
                nr_args,
                commands,
            } => match stepper.step(state, table)? {
                Some(x) => {
                    //
                    (
                        TermDef::RunProof {
                            stepper,
                            ret_type,
                            nr_args,
                            commands,
                        },
                        TermDefAction::Proof(x),
                    )
                }
                None => (
                    TermDef::ProofDone {
                        stream: stepper.take_stream(),
                        ret_type,
                        commands,
                        nr_args,
                    },
                    TermDefAction::ProofDone,
                ),
            },
            TermDef::ProofDone {
                stream,
                ret_type,
                commands,
                nr_args,
            } => {
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

                let subslice = state
                    .proof_heap
                    .as_slice()
                    .get(..nr_args)
                    .ok_or(Kind::InvalidHeapIndex)?;

                state.unify_heap.clone_from(subslice);

                let stepper = stream::unify::Stepper::new(stream::unify::Mode::Def, expr, commands);

                (
                    TermDef::RunUnify { stream, stepper },
                    TermDefAction::StartUnify,
                )
            }
            TermDef::RunUnify {
                stream,
                mut stepper,
            } => match stepper.step(state, table)? {
                Some(x) => (
                    TermDef::RunUnify { stream, stepper },
                    TermDefAction::Unify(x),
                ),
                None => (TermDef::Done { stream }, TermDefAction::Done),
            },
            TermDef::Done { stream } => (TermDef::Done { stream }, TermDefAction::Done),
            TermDef::Dummy => (TermDef::Dummy, TermDefAction::Done),
        };

        core::mem::replace(self, next_state);

        Ok(ret_val)
    }
}

#[derive(Debug)]
pub enum AxiomThm<S> {
    Start {
        idx: u32,
        is_axiom: bool,
        stream: S,
    },
    RunProof {
        stepper: stream::proof::Stepper<S>,
        is_axiom: bool,
        commands: Range<usize>,
        nr_args: usize,
    },
    ProofDone {
        stream: S,
        is_axiom: bool,
        commands: Range<usize>,
        nr_args: usize,
    },
    RunUnify {
        stream: S,
        stepper: stream::unify::Stepper,
    },
    Done {
        stream: S,
    },
    Dummy,
}

#[derive(Debug)]
pub enum AxiomThmAction {
    StartProof,
    Proof(stream::proof::Action),
    ProofDone,
    StartUnify,
    Unify(stream::unify::Action),
    Done,
}

impl<S> AxiomThm<S>
where
    S: Iterator<Item = opcode::Command<opcode::Proof>>,
{
    pub fn new(idx: u32, stream: S, is_axiom: bool) -> AxiomThm<S> {
        AxiomThm::Start {
            idx,
            stream,
            is_axiom,
        }
    }

    pub fn take_stream_if_done(self) -> Option<S> {
        match self {
            AxiomThm::Done { stream } => Some(stream),
            _ => None,
        }
    }

    pub fn is_done(&self) -> bool {
        match self {
            AxiomThm::Done { .. } => true,
            _ => false,
        }
    }

    pub fn step<SS: Store, T: Table<Type = SS::Type>>(
        &mut self,
        state: &mut State<SS>,
        table: &T,
    ) -> TResult<AxiomThmAction> {
        let old = core::mem::replace(self, Self::Dummy);

        let (next_state, ret_val) = match old {
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
                let nr_args = binders.len();
                let binders = table
                    .get_binders(binders)
                    .ok_or(Kind::InvalidBinderIndices)?;

                state.allocate_binders(table, binders)?;

                let stepper = stream::proof::Stepper::new(false, stream);

                let commands = thm.get_unify_commands();

                (
                    AxiomThm::RunProof {
                        stepper,
                        commands,
                        is_axiom,
                        nr_args,
                    },
                    AxiomThmAction::StartProof,
                )
            }
            AxiomThm::RunProof {
                mut stepper,
                commands,
                is_axiom,
                nr_args,
            } => match stepper.step(state, table)? {
                Some(x) => {
                    //
                    (
                        AxiomThm::RunProof {
                            stepper,
                            commands,
                            is_axiom,
                            nr_args,
                        },
                        AxiomThmAction::Proof(x),
                    )
                }
                None => (
                    AxiomThm::ProofDone {
                        stream: stepper.take_stream(),
                        commands,
                        is_axiom,
                        nr_args,
                    },
                    AxiomThmAction::ProofDone,
                ),
            },
            AxiomThm::ProofDone {
                stream,
                commands,
                is_axiom,
                nr_args,
            } => {
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

                let subslice = state
                    .proof_heap
                    .as_slice()
                    .get(..nr_args)
                    .ok_or(Kind::InvalidHeapIndex)?;

                state.unify_heap.clone_from(subslice);

                let stepper =
                    stream::unify::Stepper::new(stream::unify::Mode::ThmEnd, expr, commands);

                (
                    AxiomThm::RunUnify { stream, stepper },
                    AxiomThmAction::StartUnify,
                )
            }
            AxiomThm::RunUnify {
                stream,
                mut stepper,
            } => match stepper.step(state, table)? {
                Some(x) => (
                    AxiomThm::RunUnify { stream, stepper },
                    AxiomThmAction::Unify(x),
                ),
                None => (AxiomThm::Done { stream }, AxiomThmAction::Done),
            },
            AxiomThm::Done { stream } => (AxiomThm::Done { stream }, AxiomThmAction::Done),
            AxiomThm::Dummy => (AxiomThm::Dummy, AxiomThmAction::Done),
        };

        core::mem::replace(self, next_state);

        Ok(ret_val)
    }
}

#[derive(Debug)]
enum StepState<S, Ty> {
    Normal,
    TermDef(TermDef<S, Ty>),
    AxiomThm(AxiomThm<S>),
}

#[derive(Debug)]
pub struct Stepper<S, Ty>
where
    S: StatementStream + Iterator,
    <S as Iterator>::Item: TryInto<Opcode>,
{
    stream: S,
    state: StepState<S::ProofStream, Ty>,
}

#[derive(Debug)]
pub enum Action {
    AxiomStart(u32),
    ThmStart(u32),
    AxiomThmDone,
    TermDefStart(u32),
    TermDef(TermDefAction),
    TermDefDone,
    AxiomThm(AxiomThmAction),
    Sort,
}

impl<S, Ty> Stepper<S, Ty>
where
    S: StatementStream + Iterator,
    <S as Iterator>::Item: TryInto<Opcode>,
    Ty: Type,
{
    pub fn new(stream: S) -> Stepper<S, Ty> {
        Stepper {
            stream,
            state: StepState::Normal,
        }
    }

    pub fn is_state_normal(&self) -> bool {
        match self.state {
            StepState::Normal => true,
            _ => false,
        }
    }

    pub fn get_stream(&self) -> &S {
        &self.stream
    }

    pub fn get_stream_mut(&mut self) -> &mut S {
        &mut self.stream
    }

    pub fn step<SS: Store<Type = Ty>, T: Table<Type = SS::Type>>(
        &mut self,
        state: &mut State<SS>,
        table: &T,
    ) -> TResult<Option<Action>> {
        let old = core::mem::replace(&mut self.state, StepState::Normal);

        let (next_state, ret) = match old {
            StepState::Normal => return self.normal(state),
            StepState::TermDef(mut td) => {
                if td.is_done() {
                    if let Some(stream) = td.take_stream_if_done() {
                        self.stream.put_proof_stream(stream);
                    } else {
                        unreachable!("impossible");
                    }

                    state.increment_current_term();
                    (StepState::Normal, Ok(Some(Action::TermDefDone)))
                } else {
                    let ret = td.step(state, table)?;
                    (StepState::TermDef(td), Ok(Some(Action::TermDef(ret))))
                }
            }
            StepState::AxiomThm(mut at) => {
                if at.is_done() {
                    if let Some(stream) = at.take_stream_if_done() {
                        self.stream.put_proof_stream(stream);
                    } else {
                        unreachable!("impossible");
                    }

                    state.increment_current_theorem();

                    (StepState::Normal, Ok(Some(Action::AxiomThmDone)))
                } else {
                    let ret = at.step(state, table)?;
                    (StepState::AxiomThm(at), Ok(Some(Action::AxiomThm(ret))))
                }
            }
        };

        core::mem::replace(&mut self.state, next_state);

        ret
    }

    fn normal<SS: Store<Type = Ty>>(&mut self, state: &mut State<SS>) -> TResult<Option<Action>> {
        if let Some(x) = self.stream.next() {
            let x = x.try_into().map_err(|_| Kind::UnknownCommand)?;

            match x {
                Opcode::End => {
                    Ok(None)
                    //
                }
                Opcode::Sort => {
                    state.increment_current_sort();
                    Ok(Some(Action::Sort))
                }
                Opcode::TermDef => {
                    let ps = self.stream.take_proof_stream();
                    let idx = state.get_current_term();
                    let td = TermDef::new(idx, ps);

                    self.state = StepState::TermDef(td);
                    Ok(Some(Action::TermDefStart(idx)))
                }
                Opcode::Axiom => {
                    let ps = self.stream.take_proof_stream();
                    let idx = state.get_current_theorem();
                    let at = AxiomThm::new(idx, ps, true);
                    self.state = StepState::AxiomThm(at);
                    Ok(Some(Action::AxiomStart(idx)))
                }
                Opcode::Thm => {
                    let ps = self.stream.take_proof_stream();
                    let idx = state.get_current_theorem();
                    let at = AxiomThm::new(idx, ps, false);
                    self.state = StepState::AxiomThm(at);
                    Ok(Some(Action::ThmStart(idx)))
                }
            }
        } else {
            Ok(None)
        }
    }
}
