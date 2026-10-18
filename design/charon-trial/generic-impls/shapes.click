verifying "shapes.rs";

// Every instance: keeping a value returns it.
trait generic_impls::Keep<T> {
    fn keep(&self, x: T) -> T {
        ensures result == x;
    }
}

// One implementation for every type, verified once with `T` abstract.
impl<T> generic_impls::Keep<T> for generic_impls::Echo {
    fn keep(&self, x: T) -> T {
    } by { execute(); simp(); }
}

// A generic function, verified once: it returns one of its arguments.
fn generic_impls::pick<T: Copy>(first: bool, a: T, b: T) -> T {
    ensures first implies result == a;
    ensures not first implies result == b;
} by { execute(); simp(); }

// Calls at `i32` and `u32` use those contracts at their types.
fn generic_impls::through(x: i32) -> i32 {
    ensures result == x;
} by { execute(); simp(); }

fn generic_impls::through_wide(x: u32) -> u32 {
    ensures result == x;
} by { execute(); simp(); }

fn generic_impls::choose(x: i32, y: i32) -> i32 {
    ensures result == y;
} by { execute(); simp(); }
