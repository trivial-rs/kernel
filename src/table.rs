use crate::opcode;
use crate::{Var, Var_};
use core::ops::Range;

/// A handle to a sort.
///
/// Sorts have modifiers that can be queried with this handle.
/// These modifiers correspond to assertions that are verified by the kernel
/// during execution.
pub trait Sort {
    /// A pure sort does not allow expression constructors.
    fn is_pure(&self) -> bool;

    /// A strict sort can not be used as a name.
    ///
    /// TODO: explain what a name is.
    fn is_strict(&self) -> bool;

    /// Only statements with a provable sort can be proven by the kernel.
    fn is_provable(&self) -> bool;

    /// A free sort cannot be used as a dummy variable.
    fn is_free(&self) -> bool;
}

/// A handle to a term.
pub trait Term {
    type Type: Var;

    /// Returns the index of the sort this term has.
    fn get_sort_idx(&self) -> u8;

    /// Returns if this term is a definition.
    ///
    /// Definitions are always conservative and can be unfolded in a proof.
    fn is_definition(&self) -> bool;

    /// Returns the range of the binders (arguments) of the term.
    ///
    /// The range can be queried in the `Table` to get the binders themselves.
    fn get_binders(&self) -> Range<usize>;

    /// Returns the type of the expression.
    fn get_return_type(&self) -> &Self::Type;

    /// Returns the unification command stream if this term is a definition.
    fn get_command_stream(&self) -> Range<usize>;
}

/// A handle to a theorem.
///
/// Theorems in the table only contain the list of binders, and a command
/// stream for unification.
/// The number of hypotheses can be determined by counting the number of `Hyp`
/// commands in the unification stream.
pub trait Theorem {
    fn get_binders(&self) -> Range<usize>;

    fn get_unify_commands(&self) -> Range<usize>;
}

/// An interface that enables queries for properties of sorts, terms and
/// theorems.
pub trait Table {
    type Sort: Sort;
    type Term: Term<Type = Self::Var>;
    type Theorem: Theorem;
    type Var: Var;

    fn get_sort(&self, idx: u8) -> Option<&Self::Sort>;

    fn nr_sorts(&self) -> u8;

    fn get_term(&self, idx: u32) -> Option<&Self::Term>;

    fn nr_terms(&self) -> u32;

    fn get_theorem(&self, idx: u32) -> Option<&Self::Theorem>;

    fn nr_theorems(&self) -> u32;

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]>;

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>>;

    fn get_binders(&self, idx: Range<usize>) -> Option<&[Self::Var]>;
}

#[derive(Debug, Copy, Clone)]
pub struct Sort_(pub u8);

impl From<u8> for Sort_ {
    fn from(value: u8) -> Sort_ {
        Sort_(value)
    }
}

impl Sort for Sort_ {
    #[inline(always)]
    fn is_pure(&self) -> bool {
        (self.0 & 0x01) != 0
    }

    #[inline(always)]
    fn is_strict(&self) -> bool {
        (self.0 & 0x02) != 0
    }

    #[inline(always)]
    fn is_provable(&self) -> bool {
        (self.0 & 0x04) != 0
    }

    #[inline(always)]
    fn is_free(&self) -> bool {
        (self.0 & 0x08) != 0
    }
}

#[derive(Debug)]
pub struct Term_ {
    pub sort: u8,
    pub binders: Range<usize>,
    pub ret_type: Var_,
    pub unify_commands: Range<usize>,
}

impl Term for Term_ {
    type Type = Var_;

    fn get_sort_idx(&self) -> u8 {
        self.sort & 0x7F
    }

    fn is_definition(&self) -> bool {
        (self.sort & 0x80) != 0
    }

    fn get_binders(&self) -> Range<usize> {
        self.binders.clone()
    }

    fn get_return_type(&self) -> &Self::Type {
        &self.ret_type
    }

    fn get_command_stream(&self) -> Range<usize> {
        self.unify_commands.clone()
    }
}

#[derive(Debug)]
pub struct Theorem_ {
    pub binders: Range<usize>,
    pub unify_commands: Range<usize>,
}

impl Theorem for Theorem_ {
    fn get_binders(&self) -> Range<usize> {
        self.binders.clone()
    }

    fn get_unify_commands(&self) -> Range<usize> {
        self.unify_commands.clone()
    }
}

#[derive(Debug, Default)]
pub struct Table_ {
    pub sorts: Vec<Sort_>,
    pub theorems: Vec<Theorem_>,
    pub terms: Vec<Term_>,
    pub unify: Vec<opcode::Command<opcode::Unify>>,
    pub binders: Vec<Var_>,
}

impl Table for Table_ {
    type Sort = Sort_;
    type Term = Term_;
    type Theorem = Theorem_;
    type Var = Var_;

    fn get_sort(&self, idx: u8) -> Option<&Self::Sort> {
        self.sorts.get(idx as usize)
    }

    fn nr_sorts(&self) -> u8 {
        self.sorts.len() as u8
    }

    fn get_term(&self, idx: u32) -> Option<&Self::Term> {
        self.terms.get(idx as usize)
    }

    fn nr_terms(&self) -> u32 {
        self.terms.len() as u32
    }

    fn get_theorem(&self, idx: u32) -> Option<&Self::Theorem> {
        self.theorems.get(idx as usize)
    }

    fn nr_theorems(&self) -> u32 {
        self.theorems.len() as u32
    }

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]> {
        self.unify.get(idx)
    }

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>> {
        self.unify.get(idx as usize)
    }

    fn get_binders(&self, idx: Range<usize>) -> Option<&[Self::Var]> {
        self.binders.get(idx)
    }
}
