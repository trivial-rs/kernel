pub mod proof;
pub mod statement;
pub mod unify;

pub use proof::Proof;
pub use statement::Statement;
pub use unify::Unify;

use crate::TResult;

use std::convert::TryInto;

pub trait UnifyRun {
    fn run<T>(&mut self, stream: T, mode: unify::Mode) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<unify::Command>;
}

use crate::error::Kind;
use crate::verifier::Verifier;

impl<'a> UnifyRun for Verifier<'a> {
    fn run<T>(&mut self, stream: T, mode: unify::Mode) -> TResult
    where
        T: IntoIterator,
        T::Item: TryInto<unify::Command>,
    {
        self.state.unify_stack.clear();

        for i in stream {
            let command = i.try_into().map_err(|_| Kind::UnknownCommand)?;

            if self.execute(command, mode)? {
                return Ok(());
            }
        }

        Err(Kind::StreamExhausted)
    }
}
