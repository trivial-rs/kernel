pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    UnifyStackUnderflow,
    UnifyRefFailure,
}

pub type TResult<O = ()> = Result<O, Kind>;
