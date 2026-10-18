pub trait Keep<T> {
    fn keep(&self, x: T) -> T;
}

pub struct Echo {
    pub tag: u32,
}

impl<T> Keep<T> for Echo {
    fn keep(&self, x: T) -> T {
        x
    }
}

pub fn pick<T: Copy>(first: bool, a: T, b: T) -> T {
    if first {
        a
    } else {
        b
    }
}

pub fn through(x: i32) -> i32 {
    let echo = Echo { tag: 0 };
    echo.keep(x)
}

pub fn through_wide(x: u32) -> u32 {
    let echo = Echo { tag: 1 };
    echo.keep(x)
}

pub fn choose(x: i32, y: i32) -> i32 {
    pick(false, x, y)
}
