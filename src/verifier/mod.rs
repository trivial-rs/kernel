pub mod stream;

pub struct Stack {
    data: Vec<u32>,
}

impl Stack {
    fn push(&mut self, idx: u32) {
        self.data.push(idx);
    }

    fn pop(&mut self) -> Option<u32> {
        self.data.pop()
    }
}

pub struct Heap {
    data: Vec<u32>,
}

impl Heap {
    fn get(&self, idx: u32) -> Option<u32> {
        self.data.get(idx as usize).copied()
    }
}

pub struct Theorem {
    //
}

pub struct Theorems {
    data: Vec<Theorem>,
}

impl Theorems {
    fn get(&self, idx: u32) -> Option<&Theorem> {
        self.data.get(idx as usize)
    }
}

pub struct Verifier {
    proof_stack: Stack,
    proof_heap: Heap,
    unify_stack: Stack,
    unify_heap: Heap,
    theorems: Theorems,
}

impl Verifier {
    //
}
