use super::{PackedPtr, Store};
use crate::{error::Kind, KResult};

#[derive(Debug, Default)]
pub struct Stack {
    data: Vec<PackedPtr>,
}

impl Stack {
    pub fn to_display<'a, S: Store>(&'a self, store: &'a S) -> DisplayStack<'a, S> {
        DisplayStack(self, store)
    }

    pub fn push(&mut self, idx: PackedPtr) {
        self.data.push(idx);
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn pop(&mut self) -> Option<PackedPtr> {
        self.data.pop()
    }

    pub fn peek(&self) -> Option<&PackedPtr> {
        self.data.last()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn as_slice(&self) -> &[PackedPtr] {
        &self.data
    }

    pub fn get_last(&self, nr: usize) -> KResult<&[PackedPtr]> {
        let len = self.data.len();
        self.data
            .as_slice()
            .get((len - nr)..)
            .ok_or(Kind::ProofStackUnderflow)
    }

    pub fn truncate_last(&mut self, nr: usize) {
        let len = self.data.len();
        self.data.truncate(len - nr);
    }
}

use core::fmt::{self, Display, Formatter};

pub struct DisplayStack<'a, S: Store>(&'a Stack, &'a S);

impl<'a, S: Store> Display for DisplayStack<'a, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for i in self.0.data.iter().rev() {
            let ptr = i.into();

            match self.1.get_element(ptr) {
                Some(el) => writeln!(f, "> {} {}", i, el.to_display(self.1))?,
                None => writeln!(f, "> Invalid ptr")?,
            }
        }

        Ok(())
    }
}
