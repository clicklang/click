//! Trait methods whose interface reads the object through model functions:
//! `size` is `side` for a `Square` and `radius + radius` for a `Circle`, and
//! `total` and `dynamic` reach `area` through a bound and `&dyn Shape`.
//! `set` changes the object through `&mut self`, which `reset` and
//! `reset_dyn` reach through `&mut T` and `&mut dyn Shape`. `area_twice`
//! has a default body, which holds the object as `area` does and which
//! `default_square` calls on a `Square`. A `Tagged` carries a `tag` the
//! trait's functions do not read, which `tag_after_dyn` and
//! `tag_after_bound` still know after lending it as a shared object.

pub trait Shape {
    fn area(&self, scale: i32) -> i32;
    fn set(&mut self, half: i32);
    fn area_twice(&self, scale: i32) -> i32 {
        self.area(scale + scale)
    }
}

pub struct Square {
    pub side: i32,
}

pub struct Circle {
    pub radius: i32,
}

pub struct Tagged {
    pub side: i32,
    pub tag: i32,
}

impl Shape for Square {
    fn area(&self, scale: i32) -> i32 {
        self.side + scale
    }

    fn set(&mut self, half: i32) {
        self.side = half + half;
    }
}

impl Shape for Circle {
    fn area(&self, scale: i32) -> i32 {
        self.radius + self.radius + scale
    }

    fn set(&mut self, half: i32) {
        self.radius = half;
    }
}

impl Shape for Tagged {
    fn area(&self, scale: i32) -> i32 {
        self.side + scale
    }

    fn set(&mut self, half: i32) {
        self.side = half + half;
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

fn reset<T: Shape>(shape: &mut T, half: i32) {
    shape.set(half);
}

fn reset_dyn(shape: &mut dyn Shape, half: i32) {
    shape.set(half);
}

pub fn reset_square(half: i32) -> i32 {
    let mut square = Square { side: 1 };
    reset(&mut square, half);
    square.side
}

pub fn reset_dyn_square(half: i32) -> i32 {
    let mut square = Square { side: 9 };
    reset_dyn(&mut square, half);
    square.side
}

pub fn default_square(scale: i32) -> i32 {
    let square = Square { side: 3 };
    square.area_twice(scale)
}

pub fn tag_after_dyn(scale: i32) -> i32 {
    let tagged = Tagged { side: 3, tag: 7 };
    dynamic(&tagged, scale);
    tagged.tag
}

pub fn tag_after_bound(scale: i32) -> i32 {
    let tagged = Tagged { side: 3, tag: 7 };
    total(&tagged, scale);
    tagged.tag
}
