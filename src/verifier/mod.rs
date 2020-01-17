mod store;
pub mod stream;

use crate::error::Kind;
use crate::TResult;
use store::PackedStorePointer;
use store::Store;
use store::StoreElement;
pub use store::Type;
pub use stream::Stepper;

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

use crate::opcode;

use core::ops::Range;

#[derive(Debug)]
pub struct Theorem {
    pub binders: Range<usize>,
    pub unify_commands: Range<usize>,
}

impl Theorem {
    fn get_nr_args(&self) -> u16 {
        self.binders.len() as u16
    }

    fn get_binders(&self) -> Range<usize> {
        self.binders.clone()
    }

    fn get_unify_commands(&self) -> Range<usize> {
        self.unify_commands.clone()
    }
}

#[derive(Debug)]
pub struct Term_ {
    pub sort: u8,
    pub binders: Range<usize>,
    pub ret_type: Type,
    pub unify_commands: Range<usize>,
}

pub trait Term {
    fn nr_args(&self) -> u16;

    fn get_sort_idx(&self) -> u8;

    fn is_definition(&self) -> bool;

    fn get_binders(&self) -> Range<usize>;

    fn get_return_type(&self) -> Type;

    fn get_command_stream(&self) -> Range<usize>;
}

impl Term for Term_ {
    fn nr_args(&self) -> u16 {
        self.binders.len() as u16
    }

    fn get_sort_idx(&self) -> u8 {
        self.sort & 0x7F
    }

    fn is_definition(&self) -> bool {
        (self.sort & 0x80) != 0
    }

    fn get_binders(&self) -> Range<usize> {
        self.binders.clone()
    }

    fn get_return_type(&self) -> Type {
        self.ret_type
    }

    fn get_command_stream(&self) -> Range<usize> {
        self.unify_commands.clone()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Sort(pub u8);

impl From<u8> for Sort {
    fn from(value: u8) -> Sort {
        Sort(value)
    }
}

impl Sort {
    #[inline(always)]
    fn is_pure(self) -> bool {
        (self.0 & 0x01) != 0
    }

    #[inline(always)]
    fn is_strict(self) -> bool {
        (self.0 & 0x02) != 0
    }

    #[inline(always)]
    fn is_provable(self) -> bool {
        (self.0 & 0x04) != 0
    }

    #[inline(always)]
    fn is_free(self) -> bool {
        (self.0 & 0x08) != 0
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
}

#[derive(Debug, Default)]
pub struct Table {
    pub sorts: Vec<Sort>,
    pub theorems: Vec<Theorem>,
    pub terms: Vec<Term_>,
    pub proof: Vec<opcode::Command<opcode::Proof>>,
    pub unify: Vec<opcode::Command<opcode::Unify>>,
    pub binders: Vec<store::Type>,
}

impl Table {
    pub fn add_sort(&mut self, sort: Sort) {
        self.sorts.push(sort);
    }

    pub fn add_theorem(&mut self, theorem: Theorem) {
        self.theorems.push(theorem);
    }

    pub fn add_term(&mut self, term: Term_) {
        self.terms.push(term);
    }
}

pub trait TableLike {
    type Term: Term;

    fn get_term(&self, idx: u32) -> Option<&Self::Term>;

    fn get_sort(&self, idx: u8) -> Option<&Sort>;

    fn get_theorem(&self, idx: u32) -> Option<&Theorem>;

    fn get_proof_command(&self, idx: u32) -> Option<&opcode::Command<opcode::Proof>>;

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]>;

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>>;

    fn get_binders(&self, idx: Range<usize>) -> Option<&[store::Type]>;
}

impl TableLike for Table {
    type Term = Term_;

    fn get_term(&self, idx: u32) -> Option<&Self::Term> {
        self.terms.get(idx as usize)
    }

    fn get_sort(&self, idx: u8) -> Option<&Sort> {
        self.sorts.get(idx as usize)
    }

    fn get_theorem(&self, idx: u32) -> Option<&Theorem> {
        self.theorems.get(idx as usize)
    }

    fn get_proof_command(&self, idx: u32) -> Option<&opcode::Command<opcode::Proof>> {
        self.proof.get(idx as usize)
    }

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]> {
        self.unify.get(idx)
    }

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>> {
        self.unify.get(idx as usize)
    }

    fn get_binders(&self, idx: Range<usize>) -> Option<&[store::Type]> {
        self.binders.get(idx)
    }
}
