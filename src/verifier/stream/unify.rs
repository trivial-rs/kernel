use crate::error::Kind;
use crate::verifier::store::StoreTerm;
use crate::verifier::State;
use crate::TResult;

#[derive(PartialEq, Copy, Clone)]
pub enum Mode {
    Def,
    Thm,
    ThmEnd,
}

#[derive(Copy, Clone)]
pub enum Opcode {
    End,
    Ref,
    Term,
    TermSave,
    Dummy,
    Hyp,
}

#[derive(Copy, Clone)]
pub struct Command {
    opcode: Opcode,
    data: u32,
}

impl From<&Command> for Command {
    fn from(c: &Command) -> Command {
        *c
    }
}

pub trait Unify {
    fn end(&mut self, mode: Mode) -> TResult;

    fn term(&mut self, idx: u32, save: bool) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, sort: u32) -> TResult;

    fn hyp_thm(&mut self) -> TResult;

    fn hyp_thm_end(&mut self) -> TResult;

    fn execute(&mut self, command: Command, mode: Mode) -> TResult<bool> {
        use Opcode::*;
        match command.opcode {
            End => {
                self.end(mode)?;
                return Ok(true);
            }
            Ref => self.reference(command.data),
            Term => self.term(command.data, false),
            TermSave => self.term(command.data, true),
            Dummy => match mode {
                Mode::Def => self.dummy(command.data),
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

impl Unify for State {
    fn end(&mut self, mode: Mode) -> TResult {
        if mode == Mode::ThmEnd {
            if self.hyp_stack.len() != 0 {
                return Err(Kind::UnfinishedHypStack);
            }
        }

        if self.unify_stack.len() != 0 {
            return Err(Kind::UnfinishedUnifyStack);
        }

        Ok(())
    }

    fn term(&mut self, idx: u32, save: bool) -> TResult {
        let ptr = self.unify_stack.pop().ok_or(Kind::UnifyStackUnderflow)?;

        let term: StoreTerm = self.store.get(ptr.to_ptr())?;

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

        use crate::verifier::store::StoreVar;
        let var: StoreVar = self.store.get(e)?;
        let ty = var.ty;

        if !(ty.is_bound() && ty.get_sort() == (sort as u8)) {
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

            if d.depends_on_full(&deps) {
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

use std::convert::TryInto;

pub trait Run {
    fn run<T>(&mut self, stream: T, mode: Mode) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<Command>;
}

impl Run for State {
    fn run<T>(&mut self, stream: T, mode: Mode) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<Command>,
    {
        self.unify_stack.clear();

        for i in stream {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(command, mode)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}
