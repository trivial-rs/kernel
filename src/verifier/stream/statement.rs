use crate::error::Kind;
use crate::verifier::StoreElement;
use crate::verifier::Type;
use crate::TResult;
use crate::Verifier;

pub trait Statement {
    fn load_args(&mut self, binders: &[Type]) -> TResult;
}

impl Statement for Verifier {
    fn load_args(&mut self, binders: &[Type]) -> TResult {
        self.proof_heap.clear();
        self.next_bv = 1;

        for (i, ty) in binders.iter().enumerate() {
            let sort = ty.sort();
            let deps = ty.get_deps();

            if ty.is_bound() {
                if deps != self.next_bv {
                    return Err(Kind::BindDep);
                }

                self.next_bv *= 2;
            } else {
                if deps & !(self.next_bv - 1) != 0 {
                    return Err(Kind::BindDep);
                }
            }

            let var = StoreElement::Var {
                ty: *ty,
                var: i as u16,
            };

            let ptr = self.store.push(var);

            self.proof_heap.push(ptr);
        }

        Ok(())
    }
}
