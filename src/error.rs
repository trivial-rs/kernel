pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    InvalidStoreIndex,
    InvalidStoreType,
    InvalidTerm,
    InvalidStoreExpr,
    DependencyOverflow,
    UnifyStackUnderflow,
    UnifyRefFailure,
    UnifyTermFailure,
    ProofStackUnderflow,
    TypeError,
    BindDep,
    DisjointVariableViolation,
    Impossible,
}

pub type TResult<O = ()> = Result<O, Kind>;
