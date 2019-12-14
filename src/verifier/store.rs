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
pub struct Type(u64);

impl Type {
    pub fn is_bound(&self) -> bool {
        self.0 & (1u64 << 63) != 0
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

impl<'a> StoreElement<'a> {
    pub fn as_term(self) -> Option<(Type, u32, &'a [StorePointer])> {
        if let StoreElement::Term { ty, id, args } = self {
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
        ptr_args: u32,
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

impl Store {
    pub fn new() -> Store {
        Store {
            data: Vec::new(),
            args: Vec::new(),
        }
    }

    pub fn push(&mut self, element: StoreElement) -> StorePointer {
        let size = self.data.len() as u32;

        match element {
            StoreElement::Var { ty, var } => self.data.push(InternalStoreElement::Var { ty, var }),
            StoreElement::Term { ty, id, args } => {
                let offset = self.args.len() as u32;
                self.args.extend_from_slice(args);

                let ise = InternalStoreElement::Term {
                    ty,
                    num_args: args.len() as u16,
                    id,
                    ptr_args: offset,
                };

                self.data.push(ise);
            }
            StoreElement::Conv { e1, e2 } => self.data.push(InternalStoreElement::Conv { e1, e2 }),
        }

        StorePointer::expr(size)
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.args.clear();
    }

    pub fn get(&self, ptr: StorePointer) -> Option<StoreElement> {
        let element = self.data.get(ptr.get_idx())?;

        match element {
            InternalStoreElement::Var { ty, var } => Some(StoreElement::Var { ty: *ty, var: *var }),
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

                Some(StoreElement::Term {
                    ty: *ty,
                    id: *id,
                    args,
                })
            }
            InternalStoreElement::Conv { e1, e2 } => Some(StoreElement::Conv { e1: *e1, e2: *e2 }),
        }
    }
}
