use crate::verifier::{Type, Type_};

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct PackedPtr(u32);

impl PackedPtr {
    pub fn expr(e: u32) -> PackedPtr {
        PackedPtr(e << 2)
    }

    pub fn as_expr(self) -> Option<Ptr> {
        if self.0 & 0x3 == 0x0 {
            Some(self.into())
        } else {
            None
        }
    }

    pub fn proof(e: u32) -> PackedPtr {
        PackedPtr((e << 2) | 0x01)
    }

    pub fn as_proof(self) -> Option<Ptr> {
        if self.0 & 0x03 == 0x01 {
            Some(self.into())
        } else {
            None
        }
    }

    pub fn conv(e: u32) -> PackedPtr {
        PackedPtr((e << 2) | 0x02)
    }

    pub fn as_conv(self) -> Option<Ptr> {
        if self.0 & 0x03 == 0x02 {
            Some(self.into())
        } else {
            None
        }
    }

    pub fn co_conv(e: u32) -> PackedPtr {
        PackedPtr((e << 2) | 0x03)
    }

    pub fn as_co_conv(self) -> Option<Ptr> {
        if self.0 & 0x03 == 0x03 {
            Some(self.into())
        } else {
            None
        }
    }

    pub fn to_display<'a, S: Store>(&self, store: &'a S) -> DisplayPackedPtr<'a, S> {
        DisplayPackedPtr(*self, store)
    }
}

impl From<&PackedPtr> for Ptr {
    fn from(ptr: &PackedPtr) -> Ptr {
        Ptr(ptr.0 >> 2)
    }
}

impl From<PackedPtr> for Ptr {
    fn from(ptr: PackedPtr) -> Ptr {
        Ptr(ptr.0 >> 2)
    }
}

use core::fmt::{self, Display, Formatter};

pub struct DisplayPackedPtr<'a, S: Store>(PackedPtr, &'a S);

impl<'a, S: Store> Display for DisplayPackedPtr<'a, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", Into::<Ptr>::into(self.0).0)
    }
}

impl Display for PackedPtr {
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
pub struct Ptr(pub u32);

impl Ptr {
    #[inline(always)]
    pub fn to_proof(self) -> PackedPtr {
        PackedPtr::proof(self.0)
    }

    #[inline(always)]
    pub fn to_expr(self) -> PackedPtr {
        PackedPtr::expr(self.0)
    }

    #[inline(always)]
    pub fn to_co_conv(self) -> PackedPtr {
        PackedPtr::co_conv(self.0)
    }

    #[inline(always)]
    pub fn to_conv(self) -> PackedPtr {
        PackedPtr::conv(self.0)
    }

    #[inline(always)]
    pub fn get_idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub enum ElementRef<'a, Ty> {
    Var {
        ty: &'a Ty,
        var: &'a u16,
    },
    Term {
        ty: &'a Ty,
        id: &'a u32,
        args: &'a [PackedPtr],
    },
    /// Convertability proof
    Conv {
        e1: &'a PackedPtr,
        e2: &'a PackedPtr,
    },
}

impl<'a, Ty: Type> ElementRef<'a, Ty> {
    pub fn to_display<'b, S: Store<Type = Ty>>(
        &'b self,
        store: &'b S,
    ) -> DisplayElement<'a, 'b, Ty, S> {
        DisplayElement(self, store)
    }
}

pub struct DisplayElement<'a, 'b, Ty: Type, S: Store<Type = Ty>>(
    pub &'b ElementRef<'a, Ty>,
    pub &'b S,
);

impl<'a, 'b, Ty: Type, S: Store<Type = Ty>> Display for DisplayElement<'a, 'b, Ty, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.0 {
            ElementRef::Var { var, .. } => {
                write!(f, "v{}", var)
                //
            }
            ElementRef::Term { id, args, .. } => {
                write!(f, "t{} (", id)?;

                for i in *args {
                    match self.1.get_element(i.into()) {
                        Some(el) => write!(f, "{} ", el.to_display(self.1))?,
                        None => write!(f, "invalid_ptr")?,
                    }
                }

                write!(f, ")")
            }
            ElementRef::Conv { e1, e2 } => write!(f, "conv: {:?} {:?}", e1, e2),
        }
    }
}

#[derive(Debug)]
pub struct Term<'a, Ty> {
    pub ty: &'a Ty,
    pub id: &'a u32,
    pub args: &'a [PackedPtr],
}

use core::convert::TryFrom;
use core::convert::TryInto;

impl<'a, Ty> TryFrom<ElementRef<'a, Ty>> for Term<'a, Ty> {
    type Error = Kind;

    fn try_from(element: ElementRef<'a, Ty>) -> Result<Self, Self::Error> {
        if let ElementRef::Term { ty, id, args } = element {
            Ok(Term { ty, id, args })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
pub struct Conv {
    pub e1: PackedPtr,
    pub e2: PackedPtr,
}

impl<'a, Ty> TryFrom<ElementRef<'a, Ty>> for Conv {
    type Error = Kind;

    fn try_from(element: ElementRef<'a, Ty>) -> Result<Self, Self::Error> {
        if let ElementRef::Conv { e1, e2 } = element {
            Ok(Conv { e1: *e1, e2: *e2 })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
pub struct Var<Ty> {
    pub ty: Ty,
    pub var: u16,
}

impl<'a, Ty: Copy> TryFrom<ElementRef<'a, Ty>> for Var<Ty> {
    type Error = Kind;

    fn try_from(element: ElementRef<'a, Ty>) -> Result<Self, Self::Error> {
        if let ElementRef::Var { ty, var } = element {
            Ok(Var { ty: *ty, var: *var })
        } else {
            Err(Kind::InvalidStoreType)
        }
    }
}

#[derive(Debug)]
enum InternalStoreElement {
    Var {
        ty: Type_,
        var: u16,
    },
    Term {
        ty: Type_,
        num_args: u16,
        id: u32,
        ptr_args: usize,
    },
    Conv {
        e1: PackedPtr,
        e2: PackedPtr,
    },
}

#[derive(Debug, Default)]
pub struct Store_ {
    data: Vec<InternalStoreElement>,
    args: Vec<PackedPtr>,
}

use crate::error::Kind;
use crate::KResult;

pub trait Store {
    type Type: Type;

    fn create_term<T>(
        &mut self,
        id: u32,
        args: T,
        types: &[Self::Type],
        ret_type: &Self::Type,
        sort: u8,
        def: bool,
    ) -> KResult<PackedPtr>
    where
        T: IntoIterator<Item = PackedPtr>,
        T: Clone;

    fn alloc_var(&mut self, ty: Self::Type, idx: u16) -> PackedPtr;

    fn alloc_conv(&mut self, l: PackedPtr, r: PackedPtr) -> PackedPtr;

    fn clear(&mut self);

    fn get_type_of_expr(&self, ptr: Ptr) -> Option<&Self::Type>;

    fn get_element(&self, ptr: Ptr) -> Option<ElementRef<Self::Type>>;

    fn get<'a, T: TryFrom<ElementRef<'a, Self::Type>, Error = Kind>>(
        &'a self,
        ptr: Ptr,
    ) -> KResult<T>;
}

impl Store for Store_ {
    type Type = Type_;

    fn create_term<T>(
        &mut self,
        id: u32,
        args: T,
        types: &[Self::Type],
        ret_type: &Self::Type,
        sort: u8,
        def: bool,
    ) -> KResult<PackedPtr>
    where
        T: IntoIterator<Item = PackedPtr>,
        T: Clone,
    {
        let offset = self.args.len();
        let mut accum = 0;
        let mut g_deps = [0; 256];
        let mut bound = 0;

        for (arg, &target_type) in args.clone().into_iter().zip(types.iter()) {
            let arg = arg.as_expr().ok_or(Kind::InvalidStoreType)?;

            let ty = self.get_type_of_expr(arg).ok_or(Kind::InvalidStoreExpr)?;

            if !ty.is_compatible_to(&target_type) {
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

        self.args.extend(args);

        let ise = InternalStoreElement::Term {
            ty: Type::new(sort, accum, false),
            num_args: types.len() as u16,
            id,
            ptr_args: offset,
        };

        let size = self.data.len() as u32;

        self.data.push(ise);

        Ok(PackedPtr::expr(size))
    }

    fn alloc_var(&mut self, ty: Self::Type, idx: u16) -> PackedPtr {
        let size = self.data.len() as u32;

        self.data.push(InternalStoreElement::Var { ty, var: idx });

        PackedPtr::expr(size)
    }

    fn alloc_conv(&mut self, l: PackedPtr, r: PackedPtr) -> PackedPtr {
        let size = self.data.len() as u32;

        self.data.push(InternalStoreElement::Conv { e1: l, e2: r });

        PackedPtr::conv(size)
    }

    fn clear(&mut self) {
        self.data.clear();
        self.args.clear();
    }

    fn get_type_of_expr(&self, ptr: Ptr) -> Option<&Self::Type> {
        let element = self.data.get(ptr.get_idx())?;

        match element {
            InternalStoreElement::Var { ty, .. } => Some(ty),
            InternalStoreElement::Term { ty, .. } => Some(ty),
            _ => None,
        }
    }

    fn get_element(&self, ptr: Ptr) -> Option<ElementRef<Self::Type>> {
        let element = self.data.get(ptr.get_idx())?;

        match element {
            InternalStoreElement::Var { ty, var } => Some(ElementRef::Var { ty, var }),
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

                Some(ElementRef::Term { ty, id, args })
            }
            InternalStoreElement::Conv { e1, e2 } => Some(ElementRef::Conv { e1, e2 }),
        }
    }

    fn get<'a, T: TryFrom<ElementRef<'a, Self::Type>, Error = Kind>>(
        &'a self,
        ptr: Ptr,
    ) -> KResult<T> {
        let element = self.get_element(ptr).ok_or(Kind::InvalidStoreIndex)?;

        element.try_into()
    }
}

impl Display for Store_ {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for i in 0..self.data.len() {
            match self.get_element(Ptr(i as u32)) {
                Some(el) => writeln!(f, "> {}", el.to_display(self))?,
                None => writeln!(f, "> Invalid ptr")?,
            }
        }
        Ok(())
    }
}
