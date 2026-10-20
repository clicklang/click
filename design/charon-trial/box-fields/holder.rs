pub struct Cell {
    value: u32,
}

pub struct Holder {
    slot: Option<Box<Cell>>,
}

impl Holder {
    pub fn read(&mut self) -> u32 {
        match self.slot.take() {
            Some(b) => b.value,
            None => 0,
        }
    }

    pub fn put(&mut self, x: u32) {
        let _old = self.slot.take();
        self.slot = Some(Box::new(Cell { value: x }));
    }
}
