#[derive(Debug, Copy, Clone, PartialEq)]
pub struct PackedStorePointer(u32);

impl PackedStorePointer {
    pub fn expr(e: u32) -> PackedStorePointer {
        PackedStorePointer(e << 2)
    }

    pub fn as_expr(self) -> Option<StorePointer> {
        if self.0 & 0x3 == 0x0 {
            Some(self.to_ptr())
        } else {
            None
        }
    }

    pub fn proof(e: u32) -> PackedStorePointer {
        PackedStorePointer((e << 2) | 0x01)
    }

    pub fn as_proof(self) -> Option<StorePointer> {
        if self.0 & 0x03 == 0x01 {
            Some(self.to_ptr())
        } else {
            None
        }
    }

    pub fn conv(e: u32) -> PackedStorePointer {
        PackedStorePointer((e << 2) | 0x02)
    }

    pub fn as_conv(self) -> Option<StorePointer> {
        if self.0 & 0x03 == 0x02 {
            Some(self.to_ptr())
        } else {
            None
        }
    }

    pub fn co_conv(e: u32) -> PackedStorePointer {
        PackedStorePointer((e << 2) | 0x03)
    }

    pub fn as_co_conv(self) -> Option<StorePointer> {
        if self.0 & 0x03 == 0x03 {
            Some(self.to_ptr())
        } else {
            None
        }
    }

    pub fn to_ptr(self) -> StorePointer {
        StorePointer(self.0 >> 2)
    }

    pub fn to_display<'a>(&self, store: &'a Store) -> DisplayPackedStorePointer<'a> {
        DisplayPackedStorePointer(*self, store)
    }
}

use std::fmt::{self, Display, Formatter};

pub struct DisplayPackedStorePointer<'a>(PackedStorePointer, &'a Store);

impl<'a> Display for DisplayPackedStorePointer<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0.to_ptr().0)
    }
}

impl Display for PackedStorePointer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.0 & 0x03 {
            0x00 => write!(f, "expr"),
            0x01 => write!(f, "proof"),
            0x02 => write!(f, "conv"),
            0x03 => write!(f, "co-conv"),
            _ => Ok(()),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct StorePointer(pub u32);

impl StorePointer {
    #[inline(always)]
    pub fn to_proof(self) -> PackedStorePointer {
        PackedStorePointer::proof(self.0)
    }

    #[inline(always)]
    pub fn to_expr(self) -> PackedStorePointer {
        PackedStorePointer::expr(self.0)
    }

    #[inline(always)]
    pub fn to_co_conv(self) -> PackedStorePointer {
        PackedStorePointer::co_conv(self.0)
    }

    #[inline(always)]
    pub fn to_conv(self) -> PackedStorePointer {
        PackedStorePointer::conv(self.0)
    }

    #[inline(always)]
    pub fn get_idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Type(pub u64);

impl From<u64> for Type {
    #[inline(always)]
    fn from(value: u64) -> Type {
        Type(value)
    }
}

impl Type {
    #[inline(always)]
    pub fn new(sort_idx: u8, deps: u64, bound: bool) -> Type {
        if bound {
            Type((((sort_idx & 0x7F) as u64) << 56) | deps | (1 << 63))
        } else {
            Type((((sort_idx & 0x7F) as u64) << 56) | deps)
        }
    }

    #[inline(always)]
    pub fn is_bound(self) -> bool {
        self.0 & (1u64 << 63) != 0
    }

    #[inline(always)]
    pub fn depends_on(self, t: u8) -> bool {
        self.0 & (1u64 << t) != 0
    }

    #[inline(always)]
    pub fn depends_on_full(self, other: u64) -> bool {
        (self.get_deps() & other) != 0
    }

    #[inline(always)]
    pub fn get_deps(self) -> u64 {
        self.0 & ((1u64 << 56) - 1)
    }

    #[inline(always)]
    pub fn get_sort_idx(self) -> u8 {
        ((self.0 >> 56) & 0x7F) as u8
    }

    #[inline(always)]
    pub fn is_compatible_to(self, other: Self) -> bool {
        let diff = self.0 ^ other.0;

        let a = diff & !((1u64 << 56) - 1);
        let b = a & !(1u64 << 63);
        let c = self.0 & (1u64 << 63);

        (a == 0) || ((b == 0) && (c != 0))
    }
}

#[derive(Debug)]
pub enum StoreElement<'a> {
    Var {
        ty: Type,
        var: u16,
    },
    Term {
        ty: Type,
        id: u32,
        args: &'a [PackedStorePointer],
    },
    /// Convertability proof
    Conv {
        e1: PackedStorePointer,
        e2: PackedStorePointer,
    },
}

#[derive(Debug)]
pub enum StoreElementRef<'a> {
    Var {
        ty: &'a Type,
        var: &'a u16,
    },
    Term {
        ty: &'a Type,
        id: &'a u32,
        args: &'a [PackedStorePointer],
    },
    /// Convertability proof
    Conv {
        e1: &'a PackedStorePointer,
        e2: &'a PackedStorePointer,
    },
}

impl<'a> StoreElementRef<'a> {
    pub fn to_display<'b>(&'b self, store: &'b Store) -> DisplayElement<'a, 'b> {
        DisplayElement(self, store)
    }
}

pub struct DisplayElement<'a, 'b>(pub &'b StoreElementRef<'a>, pub &'b Store);

impl<'a, 'b> Display for DisplayElement<'a, 'b> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.0 {
            StoreElementRef::Var { var, .. } => {
                write!(f, "v{}", var)
                //
            }
            StoreElementRef::Term { id, args, .. } => {
                write!(f, "t{} (", id)?;

                for i in *args {
                    match self.1.get_element(i.to_ptr()) {
                        Some(el) => write!(f, "{} ", el.to_display(self.1))?,
                        None => write!(f, "invalid_ptr")?,
                    }
                }

                write!(f, ")")
            }
            StoreElementRef::Conv { e1, e2 } => write!(f, "conv: {:?} {:?}", e1, e2),
        }
    }
}

#[derive(Debug)]
pub struct StoreTerm<'a> {
    pub ty: &'a Type,
    pub id: &'a u32,
    pub args: &'a [PackedStorePointer],
}

use std::convert::TryFrom;
use std::convert::TryInto;

impl<'a> TryFrom<StoreElementRef<'a>> for StoreTerm<'a> {
    type Error = Kind;

    fn try_from(element: StoreElementRef<'a>) -> Result<Self, Self::Error> {
        if let StoreElementRef::Term { ty, id, args } = element {
            Ok(StoreTerm { ty, id, args })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
pub struct StoreConv {
    pub e1: PackedStorePointer,
    pub e2: PackedStorePointer,
}

impl<'a> TryFrom<StoreElementRef<'a>> for StoreConv {
    type Error = Kind;

    fn try_from(element: StoreElementRef<'a>) -> Result<Self, Self::Error> {
        if let StoreElementRef::Conv { e1, e2 } = element {
            Ok(StoreConv { e1: *e1, e2: *e2 })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
pub struct StoreVar {
    pub ty: Type,
    pub var: u16,
}

impl<'a> TryFrom<StoreElementRef<'a>> for StoreVar {
    type Error = Kind;

    fn try_from(element: StoreElementRef<'a>) -> Result<Self, Self::Error> {
        if let StoreElementRef::Var { ty, var } = element {
            Ok(StoreVar { ty: *ty, var: *var })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
enum InternalStoreElement {
    Var {
        ty: Type,
        var: u16,
    },
    Term {
        ty: Type,
        num_args: u16,
        id: u32,
        ptr_args: usize,
    },
    Conv {
        e1: PackedStorePointer,
        e2: PackedStorePointer,
    },
}

#[derive(Debug, Default)]
pub struct Store {
    data: Vec<InternalStoreElement>,
    args: Vec<PackedStorePointer>,
}

use crate::error::Kind;
use crate::error::TResult;

impl Store {
    pub fn create_term(
        &mut self,
        id: u32,
        args: &[PackedStorePointer],
        types: &[Type],
        ret_type: Type,
        sort: u8,
        def: bool,
    ) -> TResult<PackedStorePointer> {
        let offset = self.args.len();
        let mut accum = 0;
        let mut g_deps = [0; 256];
        let mut bound = 0;

        for (&arg, &target_type) in args.iter().zip(types.iter()) {
            let arg = arg.as_expr().ok_or(Kind::InvalidStoreType)?;

            let ty = self.get_type_of_expr(arg).ok_or(Kind::InvalidStoreExpr)?;

            if !ty.is_compatible_to(target_type) {
                return Err(Kind::IncompatibleTypes);
            }

            let mut deps = ty.get_deps();

            if target_type.is_bound() {
                *g_deps
                    .get_mut(bound as usize)
                    .ok_or(Kind::DependencyOverflow)? = deps;

                bound += 1;
            } else {
                if def {
                    for (_, &j) in g_deps
                        .get(..(bound as usize))
                        .ok_or(Kind::DependencyOverflow)?
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| target_type.depends_on(*i as u8))
                    {
                        deps &= !j;
                    }
                }

                accum |= deps;
            }
        }

        if def && ret_type.get_deps() != 0 {
            for (_, &j) in g_deps
                .get(..(bound as usize))
                .ok_or(Kind::DependencyOverflow)?
                .iter()
                .enumerate()
                .filter(|(i, _)| ret_type.depends_on(*i as u8))
            {
                accum |= j;
            }
        }

        self.args.extend_from_slice(args);

        let ise = InternalStoreElement::Term {
            ty: Type::new(sort, accum, false),
            num_args: args.len() as u16,
            id,
            ptr_args: offset,
        };

        let size = self.data.len() as u32;

        self.data.push(ise);

        Ok(PackedStorePointer::expr(size))
    }

    pub fn push<'b>(&mut self, element: StoreElement<'b>) -> PackedStorePointer {
        let size = self.data.len() as u32;

        match element {
            StoreElement::Var { ty, var } => {
                self.data.push(InternalStoreElement::Var { ty, var });
            }
            StoreElement::Term { ty, id, args } => {
                let offset = self.args.len();
                self.args.extend_from_slice(args);

                let ise = InternalStoreElement::Term {
                    ty,
                    num_args: args.len() as u16,
                    id,
                    ptr_args: offset,
                };

                self.data.push(ise);
            }
            StoreElement::Conv { e1, e2 } => {
                self.data.push(InternalStoreElement::Conv { e1, e2 });
            }
        }

        PackedStorePointer::expr(size)
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.args.clear();
    }

    pub fn get_type_of_expr(&self, ptr: StorePointer) -> Option<Type> {
        let element = self.data.get(ptr.get_idx())?;

        match element {
            InternalStoreElement::Var { ty, .. } => Some(*ty),
            InternalStoreElement::Term { ty, .. } => Some(*ty),
            _ => None,
        }
    }

    pub fn get_element(&self, ptr: StorePointer) -> Option<StoreElementRef> {
        let element = self.data.get(ptr.get_idx())?;

        match element {
            InternalStoreElement::Var { ty, var } => Some(StoreElementRef::Var { ty, var }),
            InternalStoreElement::Term {
                ty,
                num_args,
                id,
                ptr_args,
            } => {
                let ptr_args = *ptr_args as usize;
                let args = self
                    .args
                    .as_slice()
                    .get(ptr_args..(ptr_args + *num_args as usize))?;

                Some(StoreElementRef::Term { ty, id, args })
            }
            InternalStoreElement::Conv { e1, e2 } => Some(StoreElementRef::Conv { e1, e2 }),
        }
    }

    pub fn get<'a, T: TryFrom<StoreElementRef<'a>, Error = Kind>>(
        &'a self,
        ptr: StorePointer,
    ) -> TResult<T> {
        let element = self.get_element(ptr).ok_or(Kind::InvalidStoreIndex)?;

        element.try_into()
    }
}
