pub use mmb_types::opcode;
pub mod error;
pub mod verifier;

pub use error::TResult;
pub use verifier::{Sort, State, Stepper, Table, Term_, Theorem, Type};

#[cfg(test)]
mod tests {
    use super::*;

    use verifier::stream;

    pub enum Opcode<'a> {
        End,
        Sort,
        TermDef(&'a [stream::proof::Command]),
        AxiomThm(&'a [stream::proof::Command]),
    }

    pub struct StatementSliceIter<'a> {
        data: std::slice::Iter<'a, Opcode<'a>>,
        ps: Option<&'a [stream::proof::Command]>,
    }

    impl<'a> StatementSliceIter<'a> {
        fn new(data: &'a [Opcode]) -> StatementSliceIter<'a> {
            StatementSliceIter {
                data: data.iter(),
                ps: None,
            }
        }
    }

    impl<'a> Iterator for StatementSliceIter<'a> {
        type Item = stream::statement::Opcode;

        fn next(&mut self) -> Option<stream::statement::Opcode> {
            self.ps = None;

            match self.data.next() {
                Some(Opcode::End) => Some(stream::statement::Opcode::End),
                Some(Opcode::Sort) => Some(stream::statement::Opcode::Sort),
                Some(Opcode::TermDef(x)) => {
                    self.ps = Some(x);
                    Some(stream::statement::Opcode::TermDef)
                }
                Some(Opcode::AxiomThm(x)) => {
                    self.ps = Some(x);
                    Some(stream::statement::Opcode::AxiomThm)
                }
                None => None,
            }
        }
    }

    use stream::statement::StatementStream;

    impl<'a> StatementStream for StatementSliceIter<'a> {
        type AsProof = std::slice::Iter<'a, stream::proof::Command>;

        fn as_proof_stream(&self) -> Self::AsProof {
            match self.ps {
                Some(x) => x.iter(),
                None => (&[]).into_iter(),
            }
        }
    }

    #[test]
    fn it_works() {
        let mut state = State::new();
        let mut table = Table::new();

        table.add_sort(Sort(0x04));

        let ty = Type::new(0, 0, false);

        let term = Term_ {
            sort: 0,
            binders: &[],
            ret_type: ty,
            unify_commands: &[],
        };

        table.add_term(term);

        let thm = Theorem {
            binders: &[],
            unify_commands: &[],
        };

        table.add_theorem(thm);

        let program = [Opcode::Sort, Opcode::Sort];
        let stream = StatementSliceIter::new(&program);

        let mut stepper = Stepper::new(stream);

        stepper.step(&mut state, &table);
    }
}
