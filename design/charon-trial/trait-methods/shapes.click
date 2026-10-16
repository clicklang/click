verifying "shapes.rs";

// The interface of `area`: what a call through `Shape` may assume of any
// implementation. Its receiver is a value of unknown type, so it reads
// nothing through `self`. `twice` has a default body, written with its
// proof: verified once, its calls of `area` assuming `area`'s interface, and
// its contract is `twice`'s interface, which an implementation that writes
// its own `twice` refines.
trait trait_methods::Shape {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 1000;
        ensures scale < result and result <= 3001;
    }
    fn twice(&self, scale: i32) -> i32 {
        requires 0 <= scale and scale <= 1000;
        ensures result <= 6002;
    } by { execute(); simp(); }
}

// Each implementation inherits the interface's guarantees, which its own
// proof establishes with what it states itself. It may accept more calls
// than the interface, here a wider range; one that writes no `requires`
// takes the interface's.
impl trait_methods::Shape for trait_methods::Square {
    fn area(&self, scale: i32) -> i32 {
        requires 0 <= scale;
        requires scale <= 2000;
        ensures result == scale + 1;
    } by { execute(); simp(); }
}

impl trait_methods::Shape for trait_methods::Circle {
    fn area(&self, scale: i32) -> i32 {
        ensures result == scale + scale + 1;
    } by { execute(); simp(); }
    fn twice(&self, scale: i32) -> i32 {
        ensures result == scale + 3;
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

// A call of `twice` through a bound assumes its interface; on `Square`,
// which writes no `twice`, it is a call of the default body, and on
// `Circle` one of `Circle`'s own.
fn trait_methods::doubled<T: trait_methods::Shape>(shape: &T, scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures result <= 6002;
} by { execute(); simp(); }

fn trait_methods::through_default(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures result <= 6002;
} by { execute(); simp(); }

fn trait_methods::direct_default(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures result <= 6002;
} by { execute(); simp(); }

fn trait_methods::circle_default(scale: i32) -> i32 {
    requires 0 <= scale and scale <= 1000;
    ensures result <= 6002;
} by { execute(); simp(); }
