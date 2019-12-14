pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    UnifyStackUnderflow,
    UnifyRefFailure,
    BindDep,
}

pub type TResult<O = ()> = Result<O, Kind>;
