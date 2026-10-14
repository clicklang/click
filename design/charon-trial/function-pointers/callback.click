verifying "callback.rs";

contract fn Doubling(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn function_pointers::twice(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn function_pointers::apply(f: fn(i32) -> i32, x: i32) -> i32 {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn function_pointers::caller(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn function_pointers::relay(f: fn(i32) -> i32, x: i32) -> i32 {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn function_pointers::forward(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }
