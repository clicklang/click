pub struct Node {
    value: u32,
    next: Option<Box<Node>>,
}

pub struct Stack {
    head: Option<Box<Node>>,
}

impl Stack {
    pub fn new() -> Stack {
        Stack { head: None }
    }

    pub fn push(&mut self, value: u32) {
        let next = self.head.take();
        self.head = Some(Box::new(Node { value, next }));
    }

    pub fn clear(&mut self) {
        self.head = None;
    }
}

pub fn pushed(x: u32) -> u32 {
    let mut s = Stack::new();
    s.push(x);
    x
}
