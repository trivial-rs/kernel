pub trait Var: Copy {
    fn new(sort_idx: u8, deps: u64, bound: bool) -> Self;

    fn is_bound(&self) -> bool;

    fn depends_on(&self, t: u8) -> bool;

    fn depends_on_full(&self, other: u64) -> bool;

    fn dependencies(&self) -> u64;

    fn sort_idx(&self) -> u8;

    fn is_compatible_to(&self, other: &Self) -> bool;
}

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Var_(u64);

impl From<u64> for Var_ {
    #[inline(always)]
    fn from(value: u64) -> Var_ {
        Var_(value)
    }
}

impl Var for Var_ {
    #[inline(always)]
    fn new(sort_idx: u8, deps: u64, bound: bool) -> Var_ {
        if bound {
            Var_((((sort_idx & 0x7F) as u64) << 56) | deps | (1 << 63))
        } else {
            Var_((((sort_idx & 0x7F) as u64) << 56) | deps)
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
        (self.dependencies() & other) != 0
    }

    #[inline(always)]
    fn dependencies(&self) -> u64 {
        self.0 & ((1u64 << 56) - 1)
    }

    #[inline(always)]
    fn sort_idx(&self) -> u8 {
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
