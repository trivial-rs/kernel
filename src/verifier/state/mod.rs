pub mod heap;
pub mod stack;
pub mod store;

use crate::error::Kind;
use crate::verifier::table::Sort;
use crate::verifier::Table;
use crate::verifier::Type;
use crate::TResult;
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

    pub fn get_store(&self) -> &S {
        &self.store
    }

    pub fn get_hyp_stack(&self) -> &Stack {
        &self.hyp_stack
    }

    pub fn copy_current_indices<SS: Store>(other: &State<SS>) -> State<S>
    where
        State<S>: Default,
    {
        let mut dummy = Self::default();

        dummy.current_sort = other.current_sort;
        dummy.current_theorem = other.current_theorem;
        dummy.current_term = other.current_term;

        dummy
    }

    pub fn binder_check<T: Table>(
        table: &T,
        ty: &T::Type,
        current_sort: u8,
        bv: &mut u64,
    ) -> TResult {
        let idx = ty.get_sort_idx();

        if idx >= current_sort {
            return Err(Kind::SortOutOfRange);
        }

        let sort = table.get_sort(ty.get_sort_idx()).ok_or(Kind::InvalidSort)?;
        let deps = ty.get_deps();

        if ty.is_bound() {
            if sort.is_strict() {
                return Err(Kind::SortIsStrict);
            }

            if deps != *bv {
                return Err(Kind::BindDep);
            }

            *bv *= 2;
        } else if (deps & !(*bv - 1)) != 0 {
            return Err(Kind::BindDep);
        }

        Ok(())
    }

    pub fn allocate_binders<T: Table<Type = S::Type>>(
        &mut self,
        table: &T,
        binders: &[T::Type],
    ) -> TResult {
        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            Self::binder_check(table, ty, self.current_sort, &mut next_bv)?;

            let ptr = self.store.alloc_var(*ty, i as u16);
            self.proof_heap.push(ptr);
        }

        self.next_bv = next_bv;

        Ok(())
    }
}

use core::fmt::{self, Display, Formatter};

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
