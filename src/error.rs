pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    InvalidStoreIndex,
    InvalidStoreType,
    InvalidTerm,
    InvalidStoreExpr,
    InvalidSort,
    DependencyOverflow,
    UnifyStackUnderflow,
    UnifyRefFailure,
    UnifyTermFailure,
    ProofStackUnderflow,
    SortNotProvable,
    SortIsStrict,
    TypeError,
    CongUnifyError,
    BindDep,
    DisjointVariableViolation,
    Impossible,
}

pub type TResult<O = ()> = Result<O, Kind>;
