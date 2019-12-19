use crate::error::Kind;
use crate::TResult;
use crate::Verifier;

pub trait Proof {
    fn reference(&mut self, idx: u32) -> TResult;

    fn term(&mut self, idx: u32, save: bool) -> TResult;

    fn theorem(&mut self, idx: u32, save: bool) -> TResult;

    fn hyp(&mut self) -> TResult;

    fn conv(&mut self) -> TResult;

    fn refl(&mut self) -> TResult;

    fn symm(&mut self) -> TResult;
}

impl<'a> Proof for Verifier<'a> {
    fn reference(&mut self, idx: u32) -> TResult {
        let i = self.proof_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;

        self.proof_stack.push(i);

        Ok(())
    }

    fn term(&mut self, idx: u32, save: bool) -> TResult {
        let term = self.terms.get(idx).ok_or(Kind::InvalidTerm)?;
        let last = self.proof_stack.get_last(term.nr_args())?;

        let ptr = self
            .store
            .create_term(idx, last, term.get_binders(), term.get_sort(), false)?;

        self.proof_stack.truncate_last(term.nr_args());

        self.proof_stack.push(ptr);

        if save {
            self.proof_heap.push(ptr);
        }

        Ok(())
    }

    fn theorem(&mut self, idx: u32, save: bool) -> TResult {
        let thm = self.theorems.get(idx).ok_or(Kind::InvalidTheorem)?;
        let target = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;
        let last = self.proof_stack.get_last(thm.get_nr_args())?;

        let types = thm.get_binders();

        self.unify_heap.clear();

        let mut g_deps = [0; 256];
        let mut bound = 0;
        let mut i = 0;

        for (&arg, &target_type) in last.iter().zip(types.iter()) {
            let arg = arg.as_expr().ok_or(Kind::InvalidStoreExpr)?;

            let ty = self
                .store
                .get_type_of_expr(arg)
                .ok_or(Kind::InvalidStoreExpr)?;

            let deps = ty.get_deps();

            if target_type.is_bound() {
                *g_deps
                    .get_mut(bound as usize)
                    .ok_or(Kind::DependencyOverflow)? = deps;

                bound += 1;

                for &i in last.get(..i).ok_or(Kind::DependencyOverflow)? {
                    let i = i.as_expr().ok_or(Kind::InvalidStoreExpr)?;

                    let d = self
                        .store
                        .get_type_of_expr(i)
                        .ok_or(Kind::InvalidStoreExpr)?;

                    if d.depends_on_full(&deps) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            } else {
                for (i, &j) in g_deps
                    .get(..(bound as usize))
                    .ok_or(Kind::DependencyOverflow)?
                    .iter()
                    .enumerate()
                {
                    // todo other part
                    if !target_type.depends_on(i as u8) || (false) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            }

            i += 1;
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(thm.get_nr_args());

        // todo: run unify

        let proof = target.to_proof();

        self.proof_stack.push(proof);

        if save {
            self.proof_heap.push(proof);
        }

        Ok(())
    }

    fn hyp(&mut self) -> TResult {
        let e = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;
        let ty = self
            .store
            .get_type_of_expr(e)
            .ok_or(Kind::InvalidStoreExpr)?;

        let sort = self.sorts.get(ty.get_sort()).ok_or(Kind::InvalidSort)?;

        if !sort.is_provable() {
            return Err(Kind::SortNotProvable);
        }

        self.hyp_stack.push(e.to_expr());
        self.proof_heap.push(e.to_proof());

        Ok(())
    }

    fn conv(&mut self) -> TResult {
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_proof()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        self.proof_stack.push(e1.to_proof());
        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_co_conv());

        Ok(())
    }

    fn refl(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        if e1 != e2 {
            return Err(Kind::UnifyRefFailure);
        }

        Ok(())
    }

    fn symm(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreExpr)?;
        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        self.proof_stack.push(e1.to_expr());
        self.proof_stack.push(e2.to_co_conv());

        Ok(())
    }
}
