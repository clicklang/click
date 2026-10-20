pub trait Holder<T> {
    fn put(&mut self, x: T);
    fn get(&self) -> T;
}

pub struct Wrap<T> {
    pub value: T,
    pub puts: u32,
}

impl<T: Copy> Holder<T> for Wrap<T> {
    fn put(&mut self, x: T) {
        self.value = x;
    }
    fn get(&self) -> T {
        self.value
    }
}

pub fn store<H: Holder<u32>>(holder: &mut H, x: u32) -> u32 {
    holder.put(x);
    holder.get()
}

pub fn store_dyn(holder: &mut dyn Holder<u32>, x: u32) -> u32 {
    holder.put(x);
    holder.get()
}

pub fn peek<H: Holder<i32>>(holder: &H) -> i32 {
    holder.get()
}

pub fn through(x: u32) -> u32 {
    let mut wrap = Wrap { value: 0, puts: 7 };
    store(&mut wrap, x)
}

pub fn through_dyn(x: u32) -> u32 {
    let mut wrap = Wrap { value: 0, puts: 7 };
    store_dyn(&mut wrap, x)
}

pub fn through_peek(level: i32) -> u32 {
    let wrap = Wrap { value: level, puts: 7 };
    let seen = peek(&wrap);
    if seen == level {
        wrap.puts
    } else {
        0
    }
}
