pub trait Scale<T> {
    fn scale(&self, x: T) -> T;
}

pub struct Square {
    pub side: i32,
}

pub struct Wide {
    pub side: u32,
}

impl Scale<i32> for Square {
    fn scale(&self, x: i32) -> i32 {
        x + 1
    }
}

impl Scale<u32> for Wide {
    fn scale(&self, x: u32) -> u32 {
        x + 2
    }
}

pub fn total<S: Scale<i32>>(shape: &S, x: i32) -> i32 {
    shape.scale(x)
}

pub fn dynamic(shape: &dyn Scale<i32>, x: i32) -> i32 {
    shape.scale(x)
}

pub fn wide_total<S: Scale<u32>>(shape: &S, x: u32) -> u32 {
    shape.scale(x)
}

pub fn through_bound(x: i32) -> i32 {
    let square = Square { side: 3 };
    total(&square, x)
}

pub fn through_dyn(x: i32) -> i32 {
    let square = Square { side: 3 };
    dynamic(&square, x)
}

pub fn through_wide(x: u32) -> u32 {
    let wide = Wide { side: 3 };
    wide_total(&wide, x)
}
