use crate::verifier::store::{PackedStorePointer, Store};

#[derive(Debug, Default)]
pub struct Heap {
    data: Vec<PackedStorePointer>,
}

impl Heap {
    pub fn to_display<'a>(&'a self, store: &'a Store) -> DisplayHeap<'a> {
        DisplayHeap(self, store)
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn push(&mut self, idx: PackedStorePointer) {
        self.data.push(idx);
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn clone_from(&mut self, other: &[PackedStorePointer]) {
        self.data.clear();
        self.data.extend_from_slice(other);
    }

    pub fn get(&self, idx: u32) -> Option<PackedStorePointer> {
        self.data.get(idx as usize).copied()
    }

    pub fn as_slice(&self) -> &[PackedStorePointer] {
        &self.data
    }

    pub fn extend(&mut self, ext: &[PackedStorePointer]) {
        self.data.extend_from_slice(ext);
    }
}

use std::fmt::{self, Display, Formatter};

pub struct DisplayHeap<'a>(&'a Heap, &'a Store);

impl<'a> Display for DisplayHeap<'a> {
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
