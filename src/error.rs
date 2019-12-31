#[derive(Debug, Copy, Clone)]
pub enum Kind {
    InvalidHeapIndex,
    InvalidTheorem,
    InvalidStoreIndex,
    InvalidStoreType,
    InvalidTerm,
    InvalidStoreExpr,
    InvalidSort,
    InvalidStackType,
    IncompatibleTypes,
    DependencyOverflow,
    UnifyStackUnderflow,
    UnifyRefFailure,
    UnifyTermFailure,
    ProofStackUnderflow,
    SortNotProvable,
    SortIsStrict,
    SortIsPure,
    StackHasMoreThanOne,
    UnaccountedDependencies,
    BadReturnType,
    TypeError,
    TooManyBoundVariables,
    HypStackUnderflow,
    DummyCommandInTheorem,
    CongUnifyError,
    BindDep,
    DisjointVariableViolation,
    UnknownCommand,
    UnfinishedHypStack,
    UnfinishedUnifyStack,
    HypInDefStatement,
    InvalidOpcodeInDef,
    Impossible,
    StreamExhausted,
}

pub type TResult<O = ()> = Result<O, Kind>;
