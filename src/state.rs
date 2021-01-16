use crate::Table;

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct State {
    pub(crate) current_term: u32,
    pub(crate) current_theorem: u32,
    pub(crate) current_sort: u8,
}

impl State {
    pub fn get_current_term(&self) -> u32 {
        self.current_term
    }

    pub fn increment_current_term(&mut self) {
        self.current_term += 1;
    }

    pub fn get_current_theorem(&self) -> u32 {
        self.current_theorem
    }

    pub fn increment_current_theorem(&mut self) {
        self.current_theorem += 1;
    }

    pub fn get_current_sort(&self) -> u8 {
        self.current_sort
    }

    pub fn increment_current_sort(&mut self) {
        self.current_sort += 1;
    }

    pub fn from_table<T: Table>(table: &T) -> State {
        State {
            current_term: table.nr_terms(),
            current_theorem: table.nr_theorems(),
            current_sort: table.nr_sorts(),
        }
    }
}
