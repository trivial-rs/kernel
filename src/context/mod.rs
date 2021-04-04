pub mod heap;
pub mod stack;
pub mod store;

use crate::error::Kind;
use crate::table::Sort;
use crate::KResult;
use crate::Table;
use crate::Var;
pub use heap::Heap;
pub use stack::Stack;
pub use store::{PackedPtr, Ptr, Store};

#[derive(Debug, Default, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Context<S: Store> {
    pub(crate) proof_stack: Stack,
    pub(crate) proof_heap: Heap,
    pub(crate) unify_stack: Stack,
    pub(crate) unify_heap: Heap,
    pub(crate) hyp_stack: Stack,
    pub(crate) store: S,
    pub(crate) next_bv: u64,
}

impl<S: Store> Context<S> {
    pub fn proof_stack(&self) -> &Stack {
        &self.proof_stack
    }

    pub fn proof_heap(&self) -> &Heap {
        &self.proof_heap
    }

    pub fn unify_stack(&self) -> &Stack {
        &self.unify_stack
    }

    pub fn unify_heap(&self) -> &Heap {
        &self.unify_heap
    }

    pub fn store(&self) -> &S {
        &self.store
    }

    pub fn hyp_stack(&self) -> &Stack {
        &self.hyp_stack
    }

    pub fn clear_except_store(&mut self) {
        self.proof_stack.clear();
        self.proof_heap.clear();
        self.unify_stack.clear();
        self.unify_heap.clear();
        self.hyp_stack.clear();
    }

    pub fn binder_check<T: Table>(
        table: &T,
        ty: &T::Var,
        current_sort: u8,
        bv: &mut u64,
    ) -> KResult {
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

    pub fn allocate_binders<T: Table<Var = S::Var>>(
        &mut self,
        table: &T,
        current_sort: u8,
        binders: &[T::Var],
    ) -> KResult {
        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            Self::binder_check(table, ty, current_sort, &mut next_bv)?;

            let ptr = self.store.alloc_var(*ty, i as u16);
            self.proof_heap.push(ptr);
        }

        self.next_bv = next_bv;

        Ok(())
    }
}

use core::fmt::{self, Display, Formatter};

impl<S: Store> Display for Context<S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let display = self.proof_stack.to_display(&self.store);
        writeln!(f, " Stack:\n{}", display)?;
        let display = self.unify_stack.to_display(&self.store);
        writeln!(f, " UStack:\n{}", display)?;
        let display = self.hyp_stack.to_display(&self.store);
        writeln!(f, " HStack:\n{}", display)
    }
}
