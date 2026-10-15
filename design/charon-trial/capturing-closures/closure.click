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
