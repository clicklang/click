pub struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

pub struct Stack<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack { head: None, len: 0 }
    }

    pub fn push(&mut self, value: T) {
        let next = self.head.take();
        self.head = Some(Box::new(Node { value, next }));
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        let node = self.head.take()?;
        self.head = node.next;
        self.len -= 1;
        Some(node.value)
    }

    pub fn size(&self) -> usize {
        self.len
    }
}

pub fn round_trip(x: u32) -> Option<u32> {
    let mut stack = Stack::new();
    stack.push(x);
    stack.pop()
}
