pub mod heap;
pub mod stack;
pub mod store;

pub use heap::Heap;
pub use stack::Stack;
pub use store::{PackedPtr, Ptr, Store};

#[derive(Debug, Default)]
pub struct State<S: Store> {
    pub(crate) proof_stack: Stack,
    pub(crate) proof_heap: Heap,
    pub(crate) unify_stack: Stack,
    pub(crate) unify_heap: Heap,
    pub(crate) hyp_stack: Stack,
    pub(crate) store: S,
    pub(crate) next_bv: u64,
    pub(crate) current_term: u32,
    pub(crate) current_theorem: u32,
    pub(crate) current_sort: u8,
}

impl<S: Store> State<S> {
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

use std::fmt::{self, Display, Formatter};

impl<S: Store> Display for State<S> {
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
