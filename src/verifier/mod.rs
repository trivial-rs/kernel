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

    fn get_last(&self, nr: u16) -> TResult<&[StorePointer]> {
        let len = self.data.len();
        self.data
            .as_slice()
            .get((len - nr as usize)..)
            .ok_or(Kind::ProofStackUnderflow)
    }

    fn truncate_last(&mut self, nr: u16) {
        let len = self.data.len();
        self.data.truncate(len - nr as usize);
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

pub struct Term<'a> {
    nr_args: u16,
    sort: u8,
    binders: &'a [Type],
}

impl<'a> Term<'a> {
    fn nr_args(&self) -> u16 {
        self.nr_args
    }

    fn get_sort(&self) -> u8 {
        self.sort
    }

    fn get_binders(&self) -> &[Type] {
        self.binders
    }
}

pub struct Terms<'a> {
    data: Vec<Term<'a>>,
}

impl<'a> Terms<'a> {
    fn get(&self, idx: u32) -> Option<&Term> {
        self.data.get(idx as usize)
    }
}

pub struct Verifier<'a> {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    store: Store,
    theorems: Theorems,
    terms: Terms<'a>,
    next_bv: u64,
}

impl<'a> Verifier<'a> {
    //
}
