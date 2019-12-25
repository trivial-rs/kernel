use crate::error::Kind;
use crate::verifier::StoreElement;
use crate::verifier::Type;
use crate::TResult;
use crate::Verifier;

pub trait Statement {
    fn binder_check(&self, ty: &Type, bv: &mut u64) -> TResult;

    fn load_args(&mut self, binders: &[Type]) -> TResult;

    fn term_def(&mut self, idx: u32) -> TResult;

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult;

    fn allocate_var(proof_heap: &mut Heap, store: &mut Store, x: (usize, &Type));
}

use crate::verifier::store::Store;
use crate::verifier::Heap;

impl<'a> Statement for Verifier<'a> {
    fn allocate_var(proof_heap: &mut Heap, store: &mut Store, x: (usize, &Type)) {
        let var = StoreElement::Var {
            ty: *x.1,
            var: x.0 as u16,
        };

        let ptr = store.push(var);
        proof_heap.push(ptr);
    }

    fn binder_check(&self, ty: &Type, bv: &mut u64) -> TResult {
        let sort = self.sorts.get(ty.get_sort()).ok_or(Kind::InvalidSort)?;
        let deps = ty.get_deps();

        if ty.is_bound() {
            if sort.is_strict() {
                return Err(Kind::SortIsStrict);
            }

            if deps != *bv {
                return Err(Kind::BindDep);
            }

            *bv *= 2;
        } else {
            if deps & !(*bv - 1) != 0 {
                return Err(Kind::BindDep);
            }
        }

        Ok(())
    }

    fn load_args(&mut self, binders: &[Type]) -> TResult {
        self.proof_heap.clear();

        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            self.binder_check(ty, &mut next_bv)?;
            Self::allocate_var(&mut self.proof_heap, &mut self.store, (i, ty));
        }

        self.next_bv = next_bv;

        Ok(())
    }

    fn term_def(&mut self, idx: u32) -> TResult {
        let term = self.terms.get(idx).ok_or(Kind::InvalidTerm)?;
        let sort = self.sorts.get(term.get_sort()).ok_or(Kind::InvalidSort)?;

        if sort.is_pure() {
            return Err(Kind::SortIsPure);
        }

        let binders = term.get_binders();

        self.proof_heap.clear();

        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            self.binder_check(ty, &mut next_bv)?;

            Self::allocate_var(&mut self.proof_heap, &mut self.store, (i, ty));
        }

        let ret_type = term.get_return_type();

        self.binder_check(&ret_type, &mut next_bv)?;

        Self::allocate_var(
            &mut self.proof_heap,
            &mut self.store,
            (binders.len(), &ret_type),
        );

        self.next_bv = next_bv;

        if term.get_sort() != ret_type.get_sort() {
            return Err(Kind::BadReturnType);
        }

        // todo: check if allocation of return var is necessary
        self.proof_heap.pop();

        if term.is_definition() {
            // todo: run proof stream

            if self.proof_stack.len() != 1 {
                return Err(Kind::StackHasMoreThanOne);
            }

            let expr = self
                .proof_stack
                .pop()
                .ok_or(Kind::Impossible)?
                .as_expr()
                .ok_or(Kind::InvalidStoreExpr)?;

            let ty = self
                .store
                .get_type_of_expr(expr)
                .ok_or(Kind::InvalidStoreType)?;

            if !ty.is_compatible_to(&ret_type) {
                return Err(Kind::TypeError);
            }

            if ty.get_deps() != ret_type.get_deps() {
                return Err(Kind::UnaccountedDependencies);
            }

            self.unify_heap.clone_from(&self.proof_heap);

            // todo: run unify
        }

        Ok(())
    }

    fn axiom_thm(&mut self, idx: u32, is_axiom: bool) -> TResult {
        let thm = self.theorems.get(idx).ok_or(Kind::InvalidTheorem)?;

        self.store.clear();
        self.proof_stack.clear();
        self.hyp_stack.clear();

        let binders = thm.get_binders();

        let mut next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            self.binder_check(ty, &mut next_bv)?;

            Self::allocate_var(&mut self.proof_heap, &mut self.store, (i, ty));
        }

        self.next_bv = next_bv;

        // todo: run proof
        if self.proof_stack.len() != 1 {
            return Err(Kind::StackHasMoreThanOne);
        }

        let expr = self.proof_stack.pop().ok_or(Kind::Impossible)?;

        let expr = if is_axiom {
            expr.as_expr()
        } else {
            expr.as_proof()
        };

        let expr = expr.ok_or(Kind::InvalidStackType)?;

        let sort = self
            .store
            .get_type_of_expr(expr)
            .ok_or(Kind::InvalidStoreExpr)?
            .get_sort();

        let sort = self.sorts.get(sort).ok_or(Kind::InvalidSort)?;

        if !sort.is_provable() {
            return Err(Kind::SortNotProvable);
        }

        self.unify_heap.clone_from(&self.proof_heap);

        // todo: run unify

        Ok(())
    }
}
