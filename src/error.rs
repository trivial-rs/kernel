pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    InvalidStoreIndex,
    InvalidStoreType,
    UnifyStackUnderflow,
    UnifyRefFailure,
    UnifyTermFailure,
    BindDep,
}

pub type TResult<O = ()> = Result<O, Kind>;
