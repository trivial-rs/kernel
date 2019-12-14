pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
}

pub type TResult<O = ()> = Result<O, Kind>;
