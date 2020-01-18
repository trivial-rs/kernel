mod store;
pub mod stream;
pub mod table;

use crate::error::Kind;
use crate::TResult;
use store::PackedStorePointer;
use store::Store;
use store::StoreElement;
pub use store::Type;
pub use stream::Stepper;
pub use table::{Sort, Sort_, Table, Table_, Term, Term_, Theorem, Theorem_};

#[derive(Debug, Default)]
pub struct Stack {
    data: Vec<PackedStorePointer>,
}

impl Stack {
    pub fn to_display<'a>(&'a self, store: &'a Store) -> DisplayStack<'a> {
        DisplayStack(self, store)
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

    fn get_last(&self, nr: usize) -> TResult<&[PackedStorePointer]> {
        let len = self.data.len();
        self.data
            .as_slice()
            .get((len - nr)..)
            .ok_or(Kind::ProofStackUnderflow)
    }

    fn truncate_last(&mut self, nr: usize) {
        let len = self.data.len();
        self.data.truncate(len - nr);
    }
}

use std::fmt::{self, Display, Formatter};

pub struct DisplayStack<'a>(&'a Stack, &'a Store);

impl<'a> Display for DisplayStack<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for i in self.0.data.iter().rev() {
            let ptr = i.to_ptr();

            match self.1.get_element(ptr) {
                Some(el) => writeln!(f, "> {} {}", i, el.to_display(self.1))?,
                None => writeln!(f, "> Invalid ptr")?,
            }
        }

        Ok(())
    }
}

pub struct DisplayHeap<'a>(&'a Heap, &'a Store);

impl<'a> Display for DisplayHeap<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for i in self.0.data.iter().rev() {
            let ptr = i.to_ptr();

            match self.1.get_element(ptr) {
                Some(el) => writeln!(f, "> {} {}", i, el.to_display(self.1))?,
                None => writeln!(f, "> Invalid ptr")?,
            }
        }

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Heap {
    data: Vec<PackedStorePointer>,
}

impl Heap {
    pub fn to_display<'a>(&'a self, store: &'a Store) -> DisplayHeap<'a> {
        DisplayHeap(self, store)
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn clone_from(&mut self, other: &[PackedStorePointer]) {
        self.data.clear();
        self.data.extend_from_slice(other);
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

#[derive(Debug, Default)]
pub struct State {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    hyp_stack: Stack,
    store: Store,
    next_bv: u64,
    current_term: u32,
    current_theorem: u32,
    current_sort: u8,
}

impl Display for State {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(
            f,
            "=== display: term: {} theorem:{}",
            self.current_term, self.current_theorem
        )?;
        let display = self.proof_stack.to_display(&self.store);
        writeln!(f, " Stack:\n{}", display)?;
        let display = self.unify_stack.to_display(&self.store);
        writeln!(f, " UStack:\n{}", display)?;
        let display = self.hyp_stack.to_display(&self.store);
        writeln!(f, " HStack:\n{}", display)
    }
}

impl State {
    pub fn get_proof_stack(&self) -> &Stack {
        &self.proof_stack
    }

    pub fn get_proof_heap(&self) -> &Heap {
        &self.proof_heap
    }

    pub fn get_unify_stack(&self) -> &Stack {
        &self.unify_stack
    }

    pub fn get_unify_heap(&self) -> &Heap {
        &self.unify_heap
    }

    pub fn get_current_term(&self) -> u32 {
        self.current_term
    }

    pub fn increment_current_term(&mut self) {
        self.current_term += 1;
    }

    pub fn get_current_theorem(&self) -> u32 {
        self.current_theorem
    }

    pub fn increment_current_theorem(&mut self) {
        self.current_theorem += 1;
    }

    pub fn get_current_sort(&self) -> u8 {
        self.current_sort
    }

    pub fn increment_current_sort(&mut self) {
        self.current_sort += 1;
    }
}
