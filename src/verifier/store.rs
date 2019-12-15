#[derive(Copy, Clone, PartialEq)]
pub struct StorePointer(u32);

impl StorePointer {
    pub fn expr(e: u32) -> StorePointer {
        StorePointer(e << 2)
    }

    pub fn proof(e: u32) -> StorePointer {
        StorePointer((e << 2) | 0x01)
    }

    pub fn conv(e: u32) -> StorePointer {
        StorePointer((e << 2) | 0x02)
    }

    pub fn co_conv(e: u32) -> StorePointer {
        StorePointer((e << 2) | 0x03)
    }

    fn get_idx(&self) -> usize {
        ((self.0 & 0xFC) >> 2) as usize
    }
}

#[derive(Copy, Clone)]
pub struct Type(pub u64);

impl Type {
    pub fn new(sort: u8, deps: u64, bound: bool) -> Type {
        if bound {
            Type((((sort & 0x7F) as u64) << 56) | deps)
        } else {
            Type((((sort & 0x7F) as u64) << 56) | deps | (1 << 63))
        }
    }

    pub fn is_bound(&self) -> bool {
        self.0 & (1u64 << 63) != 0
    }

    pub fn depends_on(&self, t: u8) -> bool {
        self.0 & (1u64 << t) != 0
    }

    pub fn get_deps(&self) -> u64 {
        self.0 & ((1u64 << 56) - 1)
    }

    pub fn sort(&self) -> u8 {
        ((self.0 >> 56) & 0x7F) as u8
    }
}

pub enum StoreElement<'a> {
    Var {
        ty: Type,
        var: u16,
    },
    Term {
        ty: Type,
        id: u32,
        args: &'a [StorePointer],
    },
    /// Convertability proof
    Conv {
        e1: StorePointer,
        e2: StorePointer,
    },
}

pub enum StoreElementRef<'a> {
    Var {
        ty: &'a Type,
        var: &'a u16,
    },
    Term {
        ty: &'a Type,
        id: &'a u32,
        args: &'a [StorePointer],
    },
    /// Convertability proof
    Conv {
        e1: &'a StorePointer,
        e2: &'a StorePointer,
    },
}

impl<'a> StoreElementRef<'a> {
    pub fn as_term(self) -> Option<(&'a Type, &'a u32, &'a [StorePointer])> {
        if let StoreElementRef::Term { ty, id, args } = self {
            Some((ty, id, args))
        } else {
            None
        }
    }
}

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
        e1: StorePointer,
        e2: StorePointer,
    },
}

pub struct Store {
    data: Vec<InternalStoreElement>,
    args: Vec<StorePointer>,
}

use crate::error::Kind;
use crate::error::TResult;

impl Store {
    pub fn new() -> Store {
        Store {
            data: Vec::new(),
            args: Vec::new(),
        }
    }

    pub fn create_term(
        &mut self,
        id: u32,
        args: &[StorePointer],
        types: &[Type],
        sort: u8,
        def: bool,
    ) -> TResult<StorePointer> {
        let offset = self.args.len();
        let mut accum = 0;
        let mut g_deps = [0; 256];
        let mut bound = 0;

        // todo: check if all elements in last are expr

        for (&arg, &target_type) in args.iter().zip(types.iter()) {
            let ty = self.get_type_of_expr(arg).ok_or(Kind::InvalidStoreExpr)?;
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

        if def {
            let target_type = types.last().ok_or(Kind::InvalidStoreType)?;
            let target = target_type.get_deps();

            for (_, &j) in g_deps
                .get(..(bound as usize))
                .ok_or(Kind::DependencyOverflow)?
                .iter()
                .enumerate()
                .filter(|(i, _)| target_type.depends_on(*i as u8))
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

        Ok(StorePointer::expr(size))
    }

    pub fn push<'b>(&mut self, element: StoreElement<'b>) -> StorePointer {
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

        StorePointer::expr(size)
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

    pub fn get(&self, ptr: StorePointer) -> Option<StoreElementRef> {
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
}
