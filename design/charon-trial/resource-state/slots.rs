pub trait Store<T> {
    fn put(&mut self, x: T);
    fn take_or(&mut self, fallback: T) -> T;
}

pub struct Cell {
    value: u32,
}

pub struct Slot {
    item: Option<Box<Cell>>,
}

impl Store<u32> for Slot {
    fn put(&mut self, x: u32) {
        let _old = self.item.take();
        self.item = Some(Box::new(Cell { value: x }));
    }

    fn take_or(&mut self, fallback: u32) -> u32 {
        match self.item.take() {
            Some(cell) => cell.value,
            None => fallback,
        }
    }
}

pub fn refill<S: Store<u32>>(store: &mut S, x: u32) -> u32 {
    store.put(x);
    store.take_or(0)
}

pub fn refill_dyn(store: &mut dyn Store<u32>, x: u32) -> u32 {
    store.put(x);
    store.take_or(0)
}

pub fn through(slot: &mut Slot, x: u32) -> u32 {
    refill(slot, x)
}

pub fn through_dyn(slot: &mut Slot, x: u32) -> u32 {
    refill_dyn(slot, x)
}
