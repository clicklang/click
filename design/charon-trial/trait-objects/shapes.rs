//! Trait methods whose interface reads the object through model functions:
//! `size` is `side` for a `Square` and `radius + radius` for a `Circle`, and
//! `total` and `dynamic` reach `area` through a bound and `&dyn Shape`.

pub trait Shape {
    fn area(&self, scale: i32) -> i32;
}

pub struct Square {
    pub side: i32,
}

pub struct Circle {
    pub radius: i32,
}

impl Shape for Square {
    fn area(&self, scale: i32) -> i32 {
        self.side + scale
    }
}

impl Shape for Circle {
    fn area(&self, scale: i32) -> i32 {
        self.radius + self.radius + scale
    }
}

fn total<T: Shape>(shape: &T, scale: i32) -> i32 {
    shape.area(scale)
}

fn dynamic(shape: &dyn Shape, scale: i32) -> i32 {
    shape.area(scale)
}

pub fn through_bound(scale: i32) -> i32 {
    let square = Square { side: 3 };
    total(&square, scale)
}

pub fn through_dyn(scale: i32) -> i32 {
    let circle = Circle { radius: 2 };
    dynamic(&circle, scale)
}
