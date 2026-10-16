verifying "shapes.rs";

// The object of a `Shape` has a size, which each implementation defines from
// its own fields. A method with a `&self` receiver may read it as
// `size(self)`, and keeps it.
trait trait_objects::Shape {
    function size(self) -> i32;
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 100;
        requires 0 <= size(self) and size(self) <= 100;
        ensures result == size(self) + scale;
    }
}

// Each implementation defines `size` and inherits `area`'s interface, read
// on its own fields, which its proof establishes.
impl trait_objects::Shape for trait_objects::Square {
    function size(self) -> i32 { self.side }
    fn area(&self, scale: i32) -> i32 {
    } by { execute(); simp(); }
}

impl trait_objects::Shape for trait_objects::Circle {
    function size(self) -> i32 { self.radius + self.radius }
    fn area(&self, scale: i32) -> i32 {
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
