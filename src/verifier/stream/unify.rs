use crate::error::Kind;
use crate::verifier::store::StoreTerm;
use crate::TResult;
use crate::Verifier;

pub trait Unify {
    fn term(&mut self, idx: u32, save: bool) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, sort: u32) -> TResult;

    fn hyp_thm(&mut self) -> TResult;

    fn hyp_thm_end(&mut self) -> TResult;
}

impl<'a> Unify for Verifier<'a> {
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
        unimplemented!();
    }

    fn hyp_thm(&mut self) -> TResult {
        unimplemented!();
    }

    fn hyp_thm_end(&mut self) -> TResult {
        unimplemented!();
    }
}
