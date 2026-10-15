verifying "closure.rs";

contract fn Adds(x: i32) -> i32 {
    let amount: i32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == x + amount;
}

contract fn Increments(x: i32) -> i32 {
    requires 0 <= x and x <= 2000;
    ensures result == x + 1;
}

fn impl_fn::shift(f: impl Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

fn impl_fn::caller::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    requires 0 <= k and k <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == y + k;
} by { execute(); simp(); }

fn impl_fn::caller(k: i32, x: i32) -> i32 {
    requires 0 <= k and k <= 1000;
    requires 0 <= x and x <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

fn impl_fn::apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    requires Increments(f);
    requires 0 <= x and x <= 2000;
    ensures result == x + 1;
} by { execute(); simp(); }

fn impl_fn::plain::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 2000;
    ensures result == y + 1;
} by { execute(); simp(); }

fn impl_fn::plain(x: i32) -> i32 {
    requires 0 <= x and x <= 2000;
    ensures result == x + 1;
} by { execute(); simp(); }

fn impl_fn::inc(y: i32) -> i32 {
    requires 0 <= y and y <= 2000;
    ensures result == y + 1;
} by { execute(); simp(); }

fn impl_fn::named(x: i32) -> i32 {
    requires 0 <= x and x <= 2000;
    ensures result == x + 1;
} by { execute(); simp(); }

fn impl_fn::both(f: impl Fn(i32) -> i32, g: impl Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    requires Adds(f, { amount: k });
    requires Increments(g);
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k + 1;
} by { execute(); simp(); }

fn impl_fn::twice::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    requires 0 <= k and k <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == y + k;
} by { execute(); simp(); }

fn impl_fn::twice::{closure#1}(y: i32) -> i32 {
    requires 0 <= y and y <= 2000;
    ensures result == y + 1;
} by { execute(); simp(); }

fn impl_fn::twice(k: i32, x: i32) -> i32 {
    requires 0 <= k and k <= 1000;
    requires 0 <= x and x <= 1000;
    ensures result == x + k + 1;
} by { execute(); simp(); }
