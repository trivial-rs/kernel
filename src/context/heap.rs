use super::{PackedPtr, Store};

#[derive(Debug, Default)]
pub struct Heap {
    data: Vec<PackedPtr>,
}

impl Heap {
    pub fn to_display<'a, S: Store>(&'a self, store: &'a S) -> DisplayHeap<'a, S> {
        DisplayHeap(self, store)
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn push(&mut self, idx: PackedPtr) {
        self.data.push(idx);
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn clone_from(&mut self, other: &[PackedPtr]) {
        self.data.clear();
        self.data.extend_from_slice(other);
    }

    pub fn get(&self, idx: u32) -> Option<PackedPtr> {
        self.data.get(idx as usize).copied()
    }

    pub fn as_slice(&self) -> &[PackedPtr] {
        &self.data
    }

    pub fn extend(&mut self, ext: &[PackedPtr]) {
        self.data.extend_from_slice(ext);
    }
}

use core::fmt::{self, Display, Formatter};

pub struct DisplayHeap<'a, S: Store>(&'a Heap, &'a S);

impl<'a, S: Store> Display for DisplayHeap<'a, S> {
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
