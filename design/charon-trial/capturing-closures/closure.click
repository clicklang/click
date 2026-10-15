verifying "closure.rs";

contract fn Adds(x: i32) -> i32 {
    let amount: i32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}

fn capturing_closures::shift(f: &dyn Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

fn capturing_closures::caller::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == y + k;
} by { execute(); simp(); }

fn capturing_closures::caller(k: i32, x: i32) -> i32 {
    requires 0 <= k and k <= 1000;
    requires 0 <= x and x <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

fn capturing_closures::moved::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    requires 0 <= m and m <= 1000;
    ensures result == y + m;
} by { execute(); simp(); }

fn capturing_closures::moved(k: i32, x: i32) -> i32 {
    requires 0 <= k and k <= 999;
    requires 0 <= x and x <= 1000;
    ensures result == x + k + 1;
} by { execute(); simp(); }

contract fn Increments(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + 1;
}

fn capturing_closures::increment(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    requires Increments(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + 1;
} by { execute(); simp(); }

fn capturing_closures::plain::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    ensures result == y + 1;
} by { execute(); simp(); }

fn capturing_closures::plain(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + 1;
} by { execute(); simp(); }
