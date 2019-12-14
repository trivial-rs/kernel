use crate::error::Kind;
use crate::verifier::store::StoreElement;
use crate::TResult;
use crate::Verifier;

pub trait Proof {
    fn reference(&mut self, idx: u32) -> TResult;

    fn theorem(&mut self, idx: u32) -> TResult;
}

impl Proof for Verifier {
    fn reference(&mut self, idx: u32) -> TResult {
        let i = self.proof_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;

        self.proof_stack.push(i);

        Ok(())
    }

    fn theorem(&mut self, idx: u32) -> TResult {
        let thm = self.theorems.get(idx).ok_or(Kind::InvalidTheorem)?;

        Ok(())
    }
}
