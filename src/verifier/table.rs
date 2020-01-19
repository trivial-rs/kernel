use crate::opcode;
use crate::verifier::{Type, Type_};
use core::ops::Range;

pub trait Sort {
    fn is_pure(&self) -> bool;

    fn is_strict(&self) -> bool;

    fn is_provable(&self) -> bool;

    fn is_free(&self) -> bool;
}

pub trait Term {
    type Type: Type;

    fn get_sort_idx(&self) -> u8;

    fn is_definition(&self) -> bool;

    fn get_binders(&self) -> Range<usize>;

    fn get_return_type(&self) -> &Self::Type;

    fn get_command_stream(&self) -> Range<usize>;
}

pub trait Theorem {
    fn get_binders(&self) -> Range<usize>;

    fn get_unify_commands(&self) -> Range<usize>;
}

pub trait Table {
    type Sort: Sort;
    type Term: Term<Type = Self::Type>;
    type Theorem: Theorem;
    type Type: Type;

    fn get_sort(&self, idx: u8) -> Option<&Self::Sort>;

    fn get_term(&self, idx: u32) -> Option<&Self::Term>;

    fn get_theorem(&self, idx: u32) -> Option<&Self::Theorem>;

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]>;

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>>;

    fn get_binders(&self, idx: Range<usize>) -> Option<&[Self::Type]>;
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
    pub ret_type: Type_,
    pub unify_commands: Range<usize>,
}

impl Term for Term_ {
    type Type = Type_;

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
    pub binders: Vec<Type_>,
}

impl Table for Table_ {
    type Sort = Sort_;
    type Term = Term_;
    type Theorem = Theorem_;
    type Type = Type_;

    fn get_sort(&self, idx: u8) -> Option<&Self::Sort> {
        self.sorts.get(idx as usize)
    }

    fn get_term(&self, idx: u32) -> Option<&Self::Term> {
        self.terms.get(idx as usize)
    }

    fn get_theorem(&self, idx: u32) -> Option<&Self::Theorem> {
        self.theorems.get(idx as usize)
    }

    fn get_unify_commands(&self, idx: Range<usize>) -> Option<&[opcode::Command<opcode::Unify>]> {
        self.unify.get(idx)
    }

    fn get_unify_command(&self, idx: usize) -> Option<&opcode::Command<opcode::Unify>> {
        self.unify.get(idx as usize)
    }

    fn get_binders(&self, idx: Range<usize>) -> Option<&[Self::Type]> {
        self.binders.get(idx)
    }
}
