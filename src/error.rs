#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Kind {
    InvalidHeapIndex,
    InvalidProofIndex,
    InvalidTheorem,
    InvalidStoreIndex,
    InvalidStoreType,
    InvalidTerm,
    InvalidStoreExpr,
    InvalidSort,
    InvalidBinderIndices,
    InvalidUnifyCommandIndex,
    InvalidStackType,
    IncompatibleTypes,
    DependencyOverflow,
    UnifyStackUnderflow,
    CantSaveConvertabilityObligation,
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
    TheoremOutOfRange,
    TermOutOfRange,
    SortOutOfRange,
    StreamExhausted,
    MissingProofStream,
}

/// A typedef for the result from a kernel method.
pub type KResult<O = ()> = Result<O, Kind>;
