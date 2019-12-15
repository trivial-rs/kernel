use crate::error::Kind;
use crate::TResult;
use crate::Verifier;

pub trait Proof {
    fn reference(&mut self, idx: u32) -> TResult;

    fn term(&mut self, idx: u32, save: bool) -> TResult;

    fn theorem(&mut self, idx: u32) -> TResult;
}

impl<'a> Proof for Verifier<'a> {
    fn reference(&mut self, idx: u32) -> TResult {
        let i = self.proof_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;

        self.proof_stack.push(i);

        Ok(())
    }

    fn term(&mut self, idx: u32, save: bool) -> TResult {
        let term = self.terms.get(idx).ok_or(Kind::InvalidTerm)?;
        let last = self.proof_stack.get_last(term.nr_args())?;

        let ptr = self
            .store
            .create_term(idx, last, term.get_binders(), term.get_sort(), false)?;

        self.proof_stack.truncate_last(term.nr_args());

        self.proof_stack.push(ptr);

        if save {
            self.proof_heap.push(ptr);
        }

        Ok(())
    }

    fn theorem(&mut self, idx: u32) -> TResult {
        let thm = self.theorems.get(idx).ok_or(Kind::InvalidTheorem)?;

        Ok(())
    }
}
