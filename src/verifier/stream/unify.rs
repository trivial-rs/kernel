use crate::error::Kind;
use crate::TResult;
use crate::Verifier;

pub trait Unify {
    fn term(&mut self, idx: u32) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, sort: u32) -> TResult;

    fn hyp_thm(&mut self) -> TResult;

    fn hyp_thm_end(&mut self) -> TResult;
}

impl Unify for Verifier {
    fn term(&mut self, idx: u32) -> TResult {
        unimplemented!();
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
