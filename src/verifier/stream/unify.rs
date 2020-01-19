use crate::error::Kind;
use crate::verifier::state::{store, Ptr, State, Store};
use crate::verifier::{Table, Type};
use crate::TResult;
use core::convert::TryInto;
use core::ops::Range;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Mode {
    Def,
    Thm,
    ThmEnd,
}

use crate::opcode;

pub trait Unify {
    fn end(&mut self, mode: Mode) -> TResult;

    fn term(&mut self, idx: u32, save: bool) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, sort: u32) -> TResult;

    fn hyp_thm(&mut self) -> TResult;

    fn hyp_thm_end(&mut self) -> TResult;

    fn execute(&mut self, command: opcode::Command<opcode::Unify>, mode: Mode) -> TResult<bool> {
        use crate::opcode::Unify::*;
        match command.opcode {
            End => {
                self.end(mode)?;
                return Ok(true);
            }
            Ref => self.reference(command.operand),
            Term => self.term(command.operand, false),
            TermSave => self.term(command.operand, true),
            Dummy => match mode {
                Mode::Def => self.dummy(command.operand),
                _ => Err(Kind::DummyCommandInTheorem),
            },
            Hyp => match mode {
                Mode::Def => Err(Kind::HypInDefStatement),
                Mode::Thm => self.hyp_thm(),
                Mode::ThmEnd => self.hyp_thm_end(),
            },
        }?;

        Ok(false)
    }
}

impl<S: Store> Unify for State<S> {
    fn end(&mut self, mode: Mode) -> TResult {
        if mode == Mode::ThmEnd && self.hyp_stack.len() != 0 {
            return Err(Kind::UnfinishedHypStack);
        }

        if self.unify_stack.len() != 0 {
            return Err(Kind::UnfinishedUnifyStack);
        }

        Ok(())
    }

    fn term(&mut self, idx: u32, save: bool) -> TResult {
        let ptr = self.unify_stack.pop().ok_or(Kind::UnifyStackUnderflow)?;

        let term: store::Term<_> = self.store.get(ptr.to_ptr())?;

        if *term.id != idx {
            return Err(Kind::UnifyTermFailure);
        }

        for i in term.args.iter().rev() {
            self.unify_stack.push(*i);
        }

        if save {
            self.unify_heap.push(ptr);
        }

        Ok(())
    }

    fn reference(&mut self, idx: u32) -> TResult {
        let x = self.unify_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;
        let y = self.unify_stack.pop().ok_or(Kind::UnifyStackUnderflow)?;

        if x == y {
            Ok(())
        } else {
            Err(Kind::UnifyRefFailure)
        }
    }

    fn dummy(&mut self, sort: u32) -> TResult {
        let e = self
            .unify_stack
            .pop()
            .ok_or(Kind::UnifyStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStackType)?;

        use crate::verifier::state::store::StoreVar;
        let var: StoreVar<_> = self.store.get(e)?;
        let ty = var.ty;

        if !(ty.is_bound() && ty.get_sort_idx() == (sort as u8)) {
            return Err(Kind::UnifyTermFailure);
        }

        let deps = ty.get_deps();

        for i in self.unify_heap.as_slice() {
            let i = i.as_expr().ok_or(Kind::InvalidStoreExpr)?;
            // todo: check if expr is the only type of pointer

            let d = self
                .store
                .get_type_of_expr(i)
                .ok_or(Kind::InvalidStoreExpr)?;

            if d.depends_on_full(deps) {
                return Err(Kind::DisjointVariableViolation);
            }
        }

        self.unify_heap.push(e.to_expr());

        Ok(())
    }

    fn hyp_thm(&mut self) -> TResult {
        let proof = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_proof()
            .ok_or(Kind::InvalidStackType)?;

        self.unify_stack.push(proof.to_expr());

        Ok(())
    }

    fn hyp_thm_end(&mut self) -> TResult {
        if self.unify_stack.len() != 0 {
            return Err(Kind::UnfinishedUnifyStack);
        }

        let e = self.hyp_stack.pop().ok_or(Kind::HypStackUnderflow)?;

        self.unify_stack.push(e);

        Ok(())
    }
}

pub trait Run<S: Store> {
    fn run<T>(&mut self, stream: Range<usize>, table: &T, mode: Mode, target: Ptr) -> TResult
    where
        T: Table<Type = S::Type>;
}

impl<S: Store> Run<S> for State<S> {
    fn run<T>(&mut self, stream: Range<usize>, table: &T, mode: Mode, target: Ptr) -> TResult
    where
        T: Table<Type = S::Type>,
    {
        self.unify_stack.clear();
        self.unify_stack.push(target.to_expr());

        let commands = table
            .get_unify_commands(stream)
            .ok_or(Kind::InvalidUnifyCommandIndex)?;

        for i in commands {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(command, mode)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}

#[derive(Debug)]
pub struct Stepper {
    started: bool,
    mode: Mode,
    target: Ptr,
    stream: Range<usize>,
}

#[derive(Debug, Copy, Clone)]
pub enum Action {
    Started,
    Cmd(usize, opcode::Command<opcode::Unify>),
}

impl Stepper {
    pub fn new(mode: Mode, target: Ptr, stream: Range<usize>) -> Stepper {
        Stepper {
            started: false,
            mode,
            target,
            stream,
        }
    }

    pub fn step<S: Store, T: Table<Type = S::Type>>(
        &mut self,
        state: &mut State<S>,
        table: &T,
    ) -> TResult<Option<Action>> {
        if !self.started {
            state.unify_stack.clear();
            state.unify_stack.push(self.target.to_expr());
            self.started = true;
            Ok(Some(Action::Started))
        } else {
            let current_idx = self.stream.next();

            match current_idx {
                Some(idx) => {
                    let command = table
                        .get_unify_command(idx)
                        .ok_or(Kind::InvalidUnifyCommandIndex)?;

                    if state.execute(*command, self.mode)? {
                        Ok(None)
                    } else {
                        Ok(Some(Action::Cmd(idx, *command)))
                    }
                }
                None => Ok(None),
            }
        }
    }
}
