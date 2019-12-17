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

    fn extend(&mut self, ext: &[StorePointer]) {
        self.data.extend_from_slice(ext);
    }
}

pub struct Theorem<'a> {
    nr_args: u16,
    binders: &'a [Type],
}

impl<'a> Theorem<'a> {
    fn get_nr_args(&self) -> u16 {
        self.nr_args
    }

    fn get_binders(&self) -> &[Type] {
        self.binders
    }
}

pub struct Theorems<'a> {
    data: Vec<Theorem<'a>>,
}

impl<'a> Theorems<'a> {
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

pub struct Sort(u8);

impl Sort {
    fn is_pure(&self) -> bool {
        (self.0 & 0x01) != 0
    }

    fn is_strict(&self) -> bool {
        (self.0 & 0x02) != 0
    }

    fn is_provable(&self) -> bool {
        (self.0 & 0x04) != 0
    }

    fn is_free(&self) -> bool {
        (self.0 & 0x08) != 0
    }
}

pub struct Sorts {
    data: Vec<Sort>,
}

impl Sorts {
    fn get(&self, idx: u8) -> Option<&Sort> {
        self.data.get(idx as usize)
    }
}

pub struct Verifier<'a> {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    hyp_stack: Stack,
    sorts: Sorts,
    store: Store,
    theorems: Theorems<'a>,
    terms: Terms<'a>,
    next_bv: u64,
}

impl<'a> Verifier<'a> {
    //
}
