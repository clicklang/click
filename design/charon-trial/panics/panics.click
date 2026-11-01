verifying "panics.rs";

// A Rust panic is an obligation: the call that reaches it must be shown
// impossible. `assert!(c)` asserts `c`, and after it `c` is a fact.
fn above_three(x: u32) -> u32 {
    requires x > 3;
    ensures result == x - 4;
}

fn with_message(x: u32) -> u32 {
    requires x > 3;
    ensures result == x;
}

// The message's arguments are built only on the panic's path.
fn formatted(x: u32) -> u32 {
    requires x > 3;
    ensures result == x;
}

fn nonzero(x: u32) -> u32 {
    requires x != 0;
    ensures result == x;
}

fn classify(x: u8) -> u8 {
    requires x <= 1u8;
    ensures x == 0u8 implies result == 10u8;
    ensures x == 1u8 implies result == 20u8;
}

fn first(xs: &[u8]) -> u8 {
    views *xs;
    requires xs.len() > 0;
    ensures result == xs[0];
}

// `unwrap` and `expect` require `Some` and return its payload.
fn unwrapped(o: Option<u32>) -> u32 {
    requires o != Option<u32>::None;
    ensures o == Option<u32>::Some(result);
}

fn expected(o: Option<i64>) -> i64 {
    requires o == Option<i64>::Some(5i64);
    ensures result == 5i64;
}

// `assert_eq!(a, b)` asserts `a == b`, and `assert_ne!` asserts `a != b`.
fn same(x: u32, y: u32) -> u32 {
    requires x == y;
    ensures result == y;
}

fn even_half(x: u32) -> u32 {
    requires x % 2u32 == 0u32;
    ensures result == x / 2u32;
}

fn distinct(x: i64, y: i64) -> i64 {
    requires x > y;
    requires y >= 0i64;
    ensures result > 0i64;
}
