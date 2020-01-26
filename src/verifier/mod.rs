pub mod context;
pub mod state;
pub mod stream;
pub mod table;

#[derive(Debug, Copy, Clone)]
pub struct Type_(u64);

impl From<u64> for Type_ {
    #[inline(always)]
    fn from(value: u64) -> Type_ {
        Type_(value)
    }
}

pub trait Type: Copy {
    fn new(sort_idx: u8, deps: u64, bound: bool) -> Self;

    fn is_bound(&self) -> bool;

    fn depends_on(&self, t: u8) -> bool;

    fn depends_on_full(&self, other: u64) -> bool;

    fn get_deps(&self) -> u64;

    fn get_sort_idx(&self) -> u8;

    fn is_compatible_to(&self, other: &Self) -> bool;
}

impl Type for Type_ {
    #[inline(always)]
    fn new(sort_idx: u8, deps: u64, bound: bool) -> Type_ {
        if bound {
            Type_((((sort_idx & 0x7F) as u64) << 56) | deps | (1 << 63))
        } else {
            Type_((((sort_idx & 0x7F) as u64) << 56) | deps)
        }
    }

    #[inline(always)]
    fn is_bound(&self) -> bool {
        self.0 & (1u64 << 63) != 0
    }

    #[inline(always)]
    fn depends_on(&self, t: u8) -> bool {
        self.0 & (1u64 << t) != 0
    }

    #[inline(always)]
    fn depends_on_full(&self, other: u64) -> bool {
        (self.get_deps() & other) != 0
    }

    #[inline(always)]
    fn get_deps(&self) -> u64 {
        self.0 & ((1u64 << 56) - 1)
    }

    #[inline(always)]
    fn get_sort_idx(&self) -> u8 {
        ((self.0 >> 56) & 0x7F) as u8
    }

    #[inline(always)]
    fn is_compatible_to(&self, other: &Self) -> bool {
        let diff = self.0 ^ other.0;

        let a = diff & !((1u64 << 56) - 1);
        let b = a & !(1u64 << 63);
        let c = self.0 & (1u64 << 63);

        (a == 0) || ((b == 0) && (c != 0))
    }
}

pub use state::State;
pub use stream::Stepper;
pub use table::{Sort, Sort_, Table, Table_, Term, Term_, Theorem, Theorem_};
