pub trait Bag<T> {
    fn insert(&mut self, x: T);
    fn size(&self) -> u32;
}

pub struct Counter {
    pub count: u32,
    pub last: i32,
}

impl Bag<i32> for Counter {
    fn insert(&mut self, x: i32) {
        self.count = self.count + 1;
        self.last = x;
    }
    fn size(&self) -> u32 {
        self.count
    }
}

pub fn fill<B: Bag<i32>>(bag: &mut B, x: i32) -> u32 {
    bag.insert(x);
    bag.size()
}

pub fn fill_dyn(bag: &mut dyn Bag<i32>, x: i32) -> u32 {
    bag.insert(x);
    bag.size()
}

pub fn through_fill(x: i32) -> u32 {
    let mut counter = Counter { count: 0, last: 0 };
    fill(&mut counter, x)
}

pub fn through_dyn(x: i32) -> i32 {
    let mut counter = Counter { count: 3, last: 0 };
    fill_dyn(&mut counter, x);
    counter.last
}

pub trait Holder<T> {
    fn put(&mut self, x: T);
}

pub struct Slot {
    pub value: i32,
}

impl Holder<i32> for Slot {
    fn put(&mut self, x: i32) {
        self.value = x;
    }
}

pub fn store<H: Holder<i32>>(holder: &mut H, x: i32) {
    holder.put(x);
}

pub fn through_store(x: i32) -> i32 {
    let mut slot = Slot { value: 0 };
    store(&mut slot, x);
    x
}
