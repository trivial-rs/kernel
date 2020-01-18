use super::store::{PackedStorePointer, Store};
use crate::error::{Kind, TResult};

#[derive(Debug, Default)]
pub struct Stack {
    data: Vec<PackedStorePointer>,
}

impl Stack {
    pub fn to_display<'a>(&'a self, store: &'a Store) -> DisplayStack<'a> {
        DisplayStack(self, store)
    }

    pub fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn pop(&mut self) -> Option<PackedStorePointer> {
        self.data.pop()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn get_last(&self, nr: usize) -> TResult<&[PackedStorePointer]> {
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

use std::fmt::{self, Display, Formatter};

pub struct DisplayStack<'a>(&'a Stack, &'a Store);

impl<'a> Display for DisplayStack<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for i in self.0.data.iter().rev() {
            let ptr = i.to_ptr();

            match self.1.get_element(ptr) {
                Some(el) => writeln!(f, "> {} {}", i, el.to_display(self.1))?,
                None => writeln!(f, "> Invalid ptr")?,
            }
        }

        Ok(())
    }
}
