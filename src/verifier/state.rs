#[derive(Debug, Default, Clone, Copy)]
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
}