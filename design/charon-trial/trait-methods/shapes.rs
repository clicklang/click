//! Crate trait methods whose contracts are interfaces: `total` calls
//! `area` through a trait bound and `dynamic` through `&dyn Shape`, and
//! `direct` calls `Square`'s own implementation. `twice` has a default
//! body, which `Square` keeps and `Circle` overrides: `doubled` calls it
//! through a bound and `direct_default` on a `Square`.

pub trait Shape {
    fn area(&self, scale: i32) -> i32;
    fn twice(&self, scale: i32) -> i32 {
        self.area(scale) + self.area(scale)
    }
}

pub struct Square {
    pub side: i32,
}

pub struct Circle {
    pub radius: i32,
}

impl Shape for Square {
    fn area(&self, scale: i32) -> i32 {
        scale + 1
    }
}

impl Shape for Circle {
    fn area(&self, scale: i32) -> i32 {
        scale + scale + 1
    }
    fn twice(&self, scale: i32) -> i32 {
        scale + 3
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

fn doubled<T: Shape>(shape: &T, scale: i32) -> i32 {
    shape.twice(scale)
}

pub fn through_default(scale: i32) -> i32 {
    let square = Square { side: 3 };
    doubled(&square, scale)
}

pub fn direct_default(scale: i32) -> i32 {
    let square = Square { side: 1 };
    square.twice(scale)
}

pub fn circle_default(scale: i32) -> i32 {
    let circle = Circle { radius: 1 };
    doubled(&circle, scale)
}

pub fn direct(scale: i32) -> i32 {
    let square = Square { side: 1 };
    square.area(scale)
}
