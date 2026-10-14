verifying "closure.rs";

contract fn Doubling(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn closures::apply(f: fn(i32) -> i32, x: i32) -> i32 {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn closures::caller::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    ensures result == y + y;
} by { execute(); simp(); }

fn closures::caller(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }

fn closures::choose::{closure#0}(y: i32) -> i32 {
    requires 0 <= y and y <= 1000;
    ensures result == y + y;
} by { execute(); simp(); }

fn closures::choose::{closure#1}(z: i32) -> i32 {
    requires 0 <= z and z <= 1000;
    ensures result == z + z;
} by { execute(); simp(); }

fn closures::choose(by_sum: bool, x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }
