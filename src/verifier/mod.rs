mod store;
pub mod stream;

use crate::error::Kind;
use crate::TResult;
use store::Store;
use store::StoreElement;
use store::StorePointer;
use store::Type;

pub struct Stack {
    data: Vec<StorePointer>,
}

impl Stack {
    fn push(&mut self, idx: StorePointer) {
        self.data.push(idx);
    }

    fn pop(&mut self) -> Option<StorePointer> {
        self.data.pop()
    }
}

pub struct Heap {
    data: Vec<StorePointer>,
}

impl Heap {
    fn clear(&mut self) {
        self.data.clear();
    }

    fn push(&mut self, idx: StorePointer) {
        self.data.push(idx);
    }

    fn get(&self, idx: u32) -> Option<StorePointer> {
        self.data.get(idx as usize).copied()
    }
}

pub struct Theorem {
    //
}

pub struct Theorems {
    data: Vec<Theorem>,
}

impl Theorems {
    fn get(&self, idx: u32) -> Option<&Theorem> {
        self.data.get(idx as usize)
    }
}

pub struct Verifier {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    store: Store,
    theorems: Theorems,
    next_bv: u64,
}

impl Verifier {
    //
}
