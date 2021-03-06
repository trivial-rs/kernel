use crate::context::{store, Context, Ptr, Store};
use crate::error::Kind;
use crate::KResult;
use crate::Table;
use crate::Var;
use core::convert::TryInto;
use core::ops::Range;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Mode {
    Def,
    Thm,
    ThmEnd,
}

use crate::opcode;

pub trait Unify {
    fn end(&mut self, mode: Mode) -> KResult;

    fn term(&mut self, idx: u32, save: bool) -> KResult;

    fn reference(&mut self, idx: u32) -> KResult;

    fn dummy(&mut self, sort: u32) -> KResult;

    fn hyp_thm(&mut self) -> KResult;

    fn hyp_thm_end(&mut self) -> KResult;

    fn execute(&mut self, command: opcode::Command<opcode::Unify>, mode: Mode) -> KResult<bool> {
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

impl<S: Store> Unify for Context<S> {
    fn end(&mut self, mode: Mode) -> KResult {
        if mode == Mode::ThmEnd && self.hyp_stack.len() != 0 {
            return Err(Kind::UnfinishedHypStack);
        }

        if self.unify_stack.len() != 0 {
            return Err(Kind::UnfinishedUnifyStack);
        }

        Ok(())
    }

    fn term(&mut self, idx: u32, save: bool) -> KResult {
        let ptr = self.unify_stack.pop().ok_or(Kind::UnifyStackUnderflow)?;

        let term: store::Term<_> = self.store.get(ptr.into())?;

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

    fn reference(&mut self, idx: u32) -> KResult {
        let x = self.unify_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;
        let y = self.unify_stack.pop().ok_or(Kind::UnifyStackUnderflow)?;

        if x == y {
            Ok(())
        } else {
            Err(Kind::UnifyRefFailure)
        }
    }

    fn dummy(&mut self, sort: u32) -> KResult {
        let e = self
            .unify_stack
            .pop()
            .ok_or(Kind::UnifyStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStackType)?;

        let var: store::Variable<_> = self.store.get(e)?;
        let ty = var.ty;

        if !(ty.is_bound() && ty.sort_idx() == (sort as u8)) {
            return Err(Kind::UnifyTermFailure);
        }

        let deps = ty.dependencies();

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

    fn hyp_thm(&mut self) -> KResult {
        let proof = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_proof()
            .ok_or(Kind::InvalidStackType)?;

        self.unify_stack.push(proof.to_expr());

        Ok(())
    }

    fn hyp_thm_end(&mut self) -> KResult {
        if self.unify_stack.len() != 0 {
            return Err(Kind::UnfinishedUnifyStack);
        }

        let e = self.hyp_stack.pop().ok_or(Kind::HypStackUnderflow)?;

        self.unify_stack.push(e);

        Ok(())
    }
}

pub trait Run<S: Store> {
    fn run<T>(&mut self, stream: Range<usize>, table: &T, mode: Mode, target: Ptr) -> KResult
    where
        T: Table<Var = S::Var>;
}

impl<S: Store> Run<S> for Context<S> {
    fn run<T>(&mut self, stream: Range<usize>, table: &T, mode: Mode, target: Ptr) -> KResult
    where
        T: Table<Var = S::Var>,
    {
        self.unify_stack.clear();
        self.unify_stack.push(target.to_expr());

        let commands = table
            .unify_commands(stream)
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Stepper {
    started: bool,
    done: bool,
    mode: Mode,
    target: Ptr,
    stream: Range<usize>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Action {
    Started,
    Cmd(usize, opcode::Command<opcode::Unify>),
}

impl Stepper {
    pub fn new(mode: Mode, target: Ptr, stream: Range<usize>) -> Stepper {
        Stepper {
            started: false,
            done: false,
            mode,
            target,
            stream,
        }
    }

    pub fn step<S: Store, T: Table<Var = S::Var>>(
        &mut self,
        context: &mut Context<S>,
        table: &T,
    ) -> KResult<Option<Action>> {
        if self.done {
            Ok(None)
        } else if !self.started {
            context.unify_stack.clear();
            context.unify_stack.push(self.target.to_expr());
            self.started = true;
            Ok(Some(Action::Started))
        } else {
            let current_idx = self.stream.next();

            match current_idx {
                Some(idx) => {
                    let command = table
                        .unify_command(idx)
                        .ok_or(Kind::InvalidUnifyCommandIndex)?;

                    self.done = context.execute(*command, self.mode)?;

                    Ok(Some(Action::Cmd(idx, *command)))
                }
                None => Ok(None),
            }
        }
    }
}
