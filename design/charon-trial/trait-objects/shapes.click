verifying "shapes.rs";

// The object of a `Shape` has a size, which each implementation defines from
// its own fields. A method with a `&self` receiver may read it as
// `size(self)`, and keeps it; one with `&mut self` may change it, and its
// `ensures` read the new size, with `old(size(self))` the size at entry.
trait trait_objects::Shape {
    function size(self) -> i32;
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 100;
        requires 0 <= size(self) and size(self) <= 100;
        ensures result == size(self) + scale;
    }
    fn set(&mut self, half: i32) {
        requires 0 <= half and half <= 50;
        ensures size(self) == half + half;
    }
    // A default method's interface, with the proof of its default body,
    // which reads `size(self)` as `area`'s interface does.
    fn area_twice(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 50;
        requires 0 <= size(self) and size(self) <= 100;
        ensures result == size(self) + scale + scale;
    } by { execute(); simp(); }
}

// Each implementation defines `size` and inherits `area`'s interface, read
// on its own fields, which its proof establishes.
impl trait_objects::Shape for trait_objects::Square {
    function size(self) -> i32 { self.side }
    fn area(&self, scale: i32) -> i32 {
    } by { execute(); simp(); }
    fn set(&mut self, half: i32) {
    } by { execute(); simp(); }
}

impl trait_objects::Shape for trait_objects::Circle {
    function size(self) -> i32 { self.radius + self.radius }
    fn area(&self, scale: i32) -> i32 {
    } by { execute(); simp(); }
    fn set(&mut self, half: i32) {
    } by { execute(); simp(); }
}

impl trait_objects::Shape for trait_objects::Tagged {
    function size(self) -> i32 { self.side }
    fn area(&self, scale: i32) -> i32 {
    } by { execute(); simp(); }
    fn set(&mut self, half: i32) {
    } by { execute(); simp(); }
}

// A reference to a bound type parameter, or a `&dyn Shape`, holds the
// object, read through the trait's functions.
fn trait_objects::total<T: trait_objects::Shape>(shape: &T, scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }

fn trait_objects::dynamic(shape: &dyn trait_objects::Shape, scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }

// A caller that holds the struct passes it as the object, whose size is the
// struct's definition: 3 for this `Square`, 2 + 2 for this `Circle`.
fn trait_objects::through_bound(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    ensures result == 3 + scale;
} by { execute(); simp(); }

fn trait_objects::through_dyn(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    ensures result == 4 + scale;
} by { execute(); simp(); }

// A mutable reference to a bound type parameter, or a `&mut dyn Shape`,
// holds the object too, and a call through it may change its size.
fn trait_objects::reset<T: trait_objects::Shape>(shape: &mut T, half: i32) {
    requires 0 <= half and half <= 50;
    ensures size(shape) == half + half;
} by { execute(); simp(); }

fn trait_objects::reset_dyn(shape: &mut dyn trait_objects::Shape, half: i32) {
    requires 0 <= half and half <= 50;
    ensures size(shape) == half + half;
} by { execute(); simp(); }

// A caller that lends the struct mutably gets it back with fields that the
// definitions equate to the object's new size, not the fields it lent.
fn trait_objects::reset_square(half: i32) -> i32 {
    requires 0 <= half and half <= 50;
    ensures result == half + half;
} by { execute(); simp(); }

fn trait_objects::reset_dyn_square(half: i32) -> i32 {
    requires 0 <= half and half <= 50;
    ensures result == half + half;
} by { execute(); simp(); }

// `Square` keeps `area_twice`'s default body, called with its object.
fn trait_objects::default_square(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 50;
    ensures result == 3 + scale + scale;
} by { execute(); simp(); }

// A shared object lends the struct's memory for the call, so the caller keeps
// the fields the trait's functions do not read, `tag` here.
fn trait_objects::tag_after_dyn(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    ensures result == 7;
} by { execute(); simp(); }

fn trait_objects::tag_after_bound(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 100;
    ensures result == 7;
} by { execute(); simp(); }
