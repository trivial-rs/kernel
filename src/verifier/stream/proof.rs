use crate::error::Kind;
use crate::verifier::store::StoreElement;
use crate::verifier::store::StoreTerm;
use crate::verifier::store::Type;
use crate::verifier::stream;
use crate::verifier::{State, Table};
use crate::TResult;

#[derive(Copy, Clone)]
pub enum Opcode {
    End,
    Ref,
    Dummy,
    Term,
    TermSave,
    Thm,
    ThmSave,
    Hyp,
    Conv,
    Refl,
    Symm,
    Cong,
    Unfold,
    ConvCut,
    ConvRef,
    ConvSave,
}

#[derive(Copy, Clone)]
pub struct Command {
    opcode: Opcode,
    data: u32,
}

impl From<&Command> for Command {
    fn from(c: &Command) -> Command {
        *c
    }
}

pub trait Proof {
    fn end(&mut self) -> TResult;

    fn reference(&mut self, idx: u32) -> TResult;

    fn dummy(&mut self, table: &Table, sort: u32) -> TResult;

    fn term(&mut self, table: &Table, idx: u32, save: bool, def: bool) -> TResult;

    fn theorem(&mut self, table: &Table, idx: u32, save: bool) -> TResult;

    fn hyp(&mut self, table: &Table) -> TResult;

    fn conv(&mut self) -> TResult;

    fn refl(&mut self) -> TResult;

    fn symm(&mut self) -> TResult;

    fn cong(&mut self) -> TResult;

    fn unfold(&mut self, table: &Table) -> TResult;

    fn conv_cut(&mut self) -> TResult;

    fn conv_ref(&mut self, idx: u32) -> TResult;

    fn conv_save(&mut self) -> TResult;

    fn execute(&mut self, table: &Table, command: Command, is_definition: bool) -> TResult<bool> {
        use Opcode::*;
        match (command.opcode, is_definition) {
            (End, _) => {
                self.end()?;
                return Ok(true);
            }
            (Ref, _) => self.reference(command.data),
            (Dummy, _) => self.dummy(table, command.data),
            (Term, _) => self.term(table, command.data, false, is_definition),
            (TermSave, _) => self.term(table, command.data, true, is_definition),
            (Thm, false) => self.theorem(table, command.data, false),
            (ThmSave, false) => self.theorem(table, command.data, true),
            (Thm, true) => Err(Kind::InvalidOpcodeInDef),
            (ThmSave, true) => Err(Kind::InvalidOpcodeInDef),
            (Hyp, false) => self.hyp(table),
            (Hyp, true) => Err(Kind::InvalidOpcodeInDef),
            (Conv, _) => self.conv(),
            (Refl, _) => self.refl(),
            (Symm, _) => self.symm(),
            (Cong, _) => self.cong(),
            (Unfold, _) => self.unfold(table),
            (ConvCut, _) => self.conv_cut(),
            (ConvRef, _) => self.conv_ref(command.data),
            (ConvSave, _) => self.conv_save(),
        }?;

        Ok(false)
    }
}

impl Proof for State {
    fn end(&mut self) -> TResult {
        // todo: make this check the stack?
        Ok(())
    }

    fn reference(&mut self, idx: u32) -> TResult {
        let i = self.proof_heap.get(idx).ok_or(Kind::InvalidHeapIndex)?;

        self.proof_stack.push(i);

        Ok(())
    }

    fn dummy(&mut self, table: &Table, sort: u32) -> TResult {
        let s = table.sorts.get(sort as u8).ok_or(Kind::InvalidSort)?;

        if s.is_strict() {
            return Err(Kind::SortIsStrict);
        }

        if (self.next_bv >> 56) == 0 {
            return Err(Kind::TooManyBoundVariables);
        }

        let ty = Type::new(sort as u8, self.next_bv, true);

        self.next_bv *= 2;

        let var = StoreElement::Var {
            ty,
            var: self.proof_heap.len() as u16,
        };

        let ptr = self.store.push(var);

        self.proof_stack.push(ptr);
        self.proof_heap.push(ptr);

        Ok(())
    }

    fn term(&mut self, table: &Table, idx: u32, save: bool, def: bool) -> TResult {
        let term = table.terms.get(idx).ok_or(Kind::InvalidTerm)?;
        let last = self.proof_stack.get_last(term.nr_args())?;

        let ptr = self.store.create_term(
            idx,
            last,
            term.get_binders(),
            term.get_return_type(),
            term.get_sort(),
            def,
        )?;

        self.proof_stack.truncate_last(term.nr_args());

        self.proof_stack.push(ptr);

        if save {
            self.proof_heap.push(ptr);
        }

        Ok(())
    }

    fn theorem(&mut self, table: &Table, idx: u32, save: bool) -> TResult {
        let thm = table.theorems.get(idx).ok_or(Kind::InvalidTheorem)?;
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
        let mut bound: u8 = 0;
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
                    if !target_type.depends_on(i as u8) || ((j & deps) == 0) {
                        return Err(Kind::DisjointVariableViolation);
                    }
                }
            }

            i += 1;
        }

        self.unify_heap.extend(last);
        self.proof_stack.truncate_last(thm.get_nr_args());

        let commands = thm.get_unify_commands();

        stream::unify::Run::run(self, commands, stream::unify::Mode::Thm, target)?;

        let proof = target.to_proof();

        self.proof_stack.push(proof);

        if save {
            self.proof_heap.push(proof);
        }

        Ok(())
    }

    fn hyp(&mut self, table: &Table) -> TResult {
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

        let sort = table.sorts.get(ty.get_sort()).ok_or(Kind::InvalidSort)?;

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

    fn cong(&mut self) -> TResult {
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

        let e1: StoreTerm = self.store.get(e1)?;
        let e2: StoreTerm = self.store.get(e2)?;

        if e1.id != e2.id {
            return Err(Kind::CongUnifyError);
        }

        for (i, j) in e1.args.iter().zip(e2.args.iter()).rev() {
            self.proof_stack.push(j.to_ptr().to_expr());
            self.proof_stack.push(i.to_ptr().to_co_conv());
        }

        Ok(())
    }

    fn unfold(&mut self, table: &Table) -> TResult {
        let e = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t_ptr = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        let t: StoreTerm = self.store.get(t_ptr)?;

        let term = table.terms.get(*t.id).ok_or(Kind::InvalidTerm)?;

        if !term.is_definition() {
            return Err(Kind::InvalidSort);
        }

        self.unify_heap.clear();
        self.unify_heap.extend(t.args);

        let commands = term.get_unify_commands();

        stream::unify::Run::run(self, commands, stream::unify::Mode::Def, e)?;

        let t_prime = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_co_conv()
            .ok_or(Kind::InvalidStoreType)?;

        if t_ptr != t_prime {
            return Err(Kind::UnifyTermFailure);
        }

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreType)?;

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e.to_co_conv());

        Ok(())
    }

    fn conv_cut(&mut self) -> TResult {
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

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_conv());

        self.proof_stack.push(e2.to_expr());
        self.proof_stack.push(e1.to_co_conv());

        Ok(())
    }

    fn conv_ref(&mut self, idx: u32) -> TResult {
        use crate::verifier::store::{StoreConv, StorePointer};

        let x: StoreConv = self.store.get(StorePointer(idx))?;

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

        if x.e1.to_ptr() != e1 || x.e2.to_ptr() != e2 {
            return Err(Kind::UnifyRefFailure);
        }

        Ok(())
    }

    fn conv_save(&mut self) -> TResult {
        let e1 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_conv()
            .ok_or(Kind::InvalidStoreExpr)?;

        let e2 = self
            .proof_stack
            .pop()
            .ok_or(Kind::ProofStackUnderflow)?
            .as_expr()
            .ok_or(Kind::InvalidStoreExpr)?;

        let conv = StoreElement::Conv {
            e1: e1.to_expr(),
            e2: e2.to_expr(),
        };

        let ptr = self.store.push(conv);
        self.proof_heap.push(ptr);

        Ok(())
    }
}

use std::convert::TryInto;

pub trait Run {
    fn run<T>(&mut self, table: &Table, is_definition: bool, stream: T) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<Command>;
}

impl Run for State {
    fn run<T>(&mut self, table: &Table, is_definition: bool, stream: T) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<Command>,
    {
        for i in stream {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(table, command, is_definition)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}
