mod store;
pub mod stream;

use crate::error::Kind;
use crate::TResult;
use store::PackedStorePointer;
use store::Store;
use store::StoreElement;
pub use store::Type;
pub use stream::Stepper;

pub struct Stack {
    data: Vec<PackedStorePointer>,
}

impl Stack {
    fn new() -> Stack {
        Stack { data: Vec::new() }
    }

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
    fn new() -> Heap {
        Heap { data: Vec::new() }
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    fn pop(&mut self) {
        self.data.pop();
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn clone_from(&mut self, other: &Heap) {
        self.data.clone_from(&other.data);
    }

    fn get(&self, idx: u32) -> Option<PackedStorePointer> {
        self.data.get(idx as usize).copied()
    }

    fn as_slice(&self) -> &[PackedStorePointer] {
        &self.data
    }

    fn extend(&mut self, ext: &[PackedStorePointer]) {
        self.data.extend_from_slice(ext);
    }
}

pub struct Theorem<'a> {
    pub binders: &'a [Type],
    pub unify_commands: &'a [stream::unify::Command],
}

impl<'a> Theorem<'a> {
    fn get_nr_args(&self) -> u16 {
        self.binders.len() as u16
    }

    fn get_binders(&self) -> &[Type] {
        self.binders
    }

    fn get_unify_commands(&self) -> &[stream::unify::Command] {
        self.unify_commands
    }
}

pub struct Term_<'a> {
    pub sort: u8,
    pub binders: &'a [Type],
    pub ret_type: Type,
    pub unify_commands: &'a [stream::unify::Command],
}

pub trait Term {
    fn nr_args(&self) -> u16;

    fn get_sort(&self) -> u8;

    fn is_definition(&self) -> bool;

    fn get_binders(&self) -> &[Type];

    fn get_return_type(&self) -> Type;
}

impl<'a> Term for Term_<'a> {
    fn nr_args(&self) -> u16 {
        self.binders.len() as u16
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

pub struct Sort(pub u8);

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

pub struct State {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    hyp_stack: Stack,
    store: Store,
    next_bv: u64,
}

impl State {
    pub fn new() -> State {
        State {
            proof_stack: Stack::new(),
            proof_heap: Heap::new(),
            unify_stack: Stack::new(),
            unify_heap: Heap::new(),
            hyp_stack: Stack::new(),
            store: Store::new(),
            next_bv: 0,
        }
    }
}

pub struct Table<'a> {
    sorts: Vec<Sort>,
    theorems: Vec<Theorem<'a>>,
    terms: Vec<Term_<'a>>,
}

impl<'a> Table<'a> {
    pub fn new() -> Table<'a> {
        Table {
            sorts: Vec::new(),
            theorems: Vec::new(),
            terms: Vec::new(),
        }
    }

    pub fn add_sort(&mut self, sort: Sort) {
        self.sorts.push(sort);
    }

    pub fn add_theorem(&mut self, theorem: Theorem<'a>) {
        self.theorems.push(theorem);
    }

    pub fn add_term(&mut self, term: Term_<'a>) {
        self.terms.push(term);
    }
}

pub trait CommandStream<'a> {
    type Iterator: Iterator<Item = &'a stream::unify::Command>;

    fn get_command_stream(&self) -> Self::Iterator;
}

impl<'a> CommandStream<'a> for Term_<'a> {
    type Iterator = std::slice::Iter<'a, stream::unify::Command>;

    fn get_command_stream(&self) -> Self::Iterator {
        self.unify_commands.iter()
    }
}

pub trait TableLike<'a> {
    type Term: CommandStream<'a, Iterator = Self::Iterator> + Term;
    type Iterator: Iterator<Item = &'a stream::unify::Command>;

    fn get_term(&self, idx: u32) -> Option<&Self::Term>;

    fn get_sort(&self, idx: u8) -> Option<&Sort>;

    fn get_theorem(&self, idx: u32) -> Option<&Theorem>;
}

impl<'a> TableLike<'a> for Table<'a> {
    type Term = Term_<'a>;
    type Iterator = std::slice::Iter<'a, stream::unify::Command>;

    fn get_term(&self, idx: u32) -> Option<&Self::Term> {
        self.terms.get(idx as usize)
    }

    fn get_sort(&self, idx: u8) -> Option<&Sort> {
        self.sorts.get(idx as usize)
    }

    fn get_theorem(&self, idx: u32) -> Option<&Theorem> {
        self.theorems.get(idx as usize)
    }
}

pub struct Verifier<'a> {
    state: State,
    table: Table<'a>,
}

impl<'a> Verifier<'a> {
    //
}
