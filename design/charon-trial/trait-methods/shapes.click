verifying "shapes.rs";

// The interface of `area`: what a call through `Shape` may assume of any
// implementation. Its receiver is a value of unknown type, so it reads
// nothing through `self`.
trait trait_methods::Shape {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 1000;
        ensures scale < result and result <= 3001;
    }
}

// Each implementation refines the interface: it accepts every call the
// interface allows, here a wider range, and states the interface's
// guarantee, which its own proof establishes.
impl trait_methods::Shape for trait_methods::Square {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale;
        requires scale <= 2000;
        ensures result == scale + 1;
        ensures scale < result and result <= 3001;
    } by { execute(); simp(); }
}

impl trait_methods::Shape for trait_methods::Circle {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 1000;
        ensures result == scale + scale + 1;
        ensures scale < result and result <= 3001;
    } by { execute(); simp(); }
}

fn trait_methods::total<T: trait_methods::Shape>(shape: &T, scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result and result <= 3001;
} by { execute(); simp(); }

fn trait_methods::dynamic(shape: &dyn trait_methods::Shape, scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result and result <= 3001;
} by { execute(); simp(); }

fn trait_methods::through_bound(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result;
} by { execute(); simp(); }

fn trait_methods::through_dyn(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result;
} by { execute(); simp(); }

// A call on a known type is a call of that type's implementation, with its
// own contract.
fn trait_methods::direct(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures result == scale + 1;
} by { execute(); simp(); }
