mod store;
pub mod stream;

use crate::error::Kind;
use crate::TResult;
use store::PackedStorePointer;
use store::Store;
use store::StoreElement;
use store::Type;

pub struct Stack {
    data: Vec<PackedStorePointer>,
}

impl Stack {
    fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn pop(&mut self) -> Option<PackedStorePointer> {
        self.data.pop()
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn get_last(&self, nr: u16) -> TResult<&[PackedStorePointer]> {
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
    data: Vec<PackedStorePointer>,
}

impl Heap {
    fn clear(&mut self) {
        self.data.clear();
    }

    fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    fn pop(&mut self) {
        self.data.pop();
    }

    fn clone_from(&mut self, other: &Heap) {
        self.data.clone_from(&other.data);
    }

    fn get(&self, idx: u32) -> Option<PackedStorePointer> {
        self.data.get(idx as usize).copied()
    }

    fn extend(&mut self, ext: &[PackedStorePointer]) {
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
    ret_type: Type,
}

impl<'a> Term<'a> {
    fn nr_args(&self) -> u16 {
        self.nr_args
    }

    fn get_sort(&self) -> u8 {
        self.sort & 0x7F
    }

    fn is_definition(&self) -> bool {
        (self.sort & 0x80) != 0
    }

    fn get_binders(&self) -> &[Type] {
        self.binders
    }

    fn get_return_type(&self) -> Type {
        self.ret_type
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

pub struct State {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    hyp_stack: Stack,
    store: Store,
    next_bv: u64,
}

pub struct Verifier<'a> {
    state: State,
    sorts: Sorts,
    theorems: Theorems<'a>,
    terms: Terms<'a>,
}

impl<'a> Verifier<'a> {
    //
}
