verifying "shapes.rs";

// Every instance: the result differs from the argument.
trait generic_traits::Scale<T> {
    fn scale(&self, x: T) -> T {
        ensures result != x;
    }
}

// The `i32` instance adds its own bounds.
trait generic_traits::Scale<i32> {
    fn scale(&self, x: i32) -> i32 {
        requires 0 <= x and x <= 1000;
        ensures x < result;
    }
}

trait generic_traits::Scale<u32> {
    fn scale(&self, x: u32) -> u32 {
        requires x <= 1000;
    }
}

impl generic_traits::Scale<i32> for generic_traits::Square {
    fn scale(&self, x: i32) -> i32 {
        ensures result == x + 1;
    } by { execute(); simp(); }
}

impl generic_traits::Scale<u32> for generic_traits::Wide {
    fn scale(&self, x: u32) -> u32 {
        ensures result == x + 2;
    } by { execute(); simp(); }
}

fn generic_traits::total<S: generic_traits::Scale<i32>>(shape: &S, x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures x < result;
} by { execute(); simp(); }

fn generic_traits::dynamic(shape: &dyn generic_traits::Scale<i32>, x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures x < result;
} by { execute(); simp(); }

fn generic_traits::wide_total<S: generic_traits::Scale<u32>>(shape: &S, x: u32) -> u32 {
    requires x <= 1000;
    ensures result != x;
} by { execute(); simp(); }

fn generic_traits::through_bound(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures x < result;
} by { execute(); simp(); }

fn generic_traits::through_dyn(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures x < result;
} by { execute(); simp(); }

fn generic_traits::through_wide(x: u32) -> u32 {
    requires x <= 1000;
    ensures result != x;
} by { execute(); simp(); }
