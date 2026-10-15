verifying "adds.rs";

contract fn Adds(x: i32) -> i32 {
    let amount: i32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}

fn adds::add3(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by { execute(); simp(); }

fn adds::apply(f: fn(i32) -> i32, x: i32, k: i32) -> i32 {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

fn adds::caller(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by { execute(); simp(); }
