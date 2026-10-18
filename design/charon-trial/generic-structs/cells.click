verifying "cells.rs";

// A generic struct's functions, verified once with `T` abstract: a value of
// `T` stored in a field reads back as itself.
fn generic_structs::make<T: Copy>(value: T) -> generic_structs::Cell<T> {
    ensures result.value == value;
    ensures result.count == 0;
} by { execute(); simp(); }

fn generic_structs::read<T: Copy>(cell: &generic_structs::Cell<T>) -> T {
    views cell.value;
    ensures result == cell.value;
} by { execute(); simp(); }

fn generic_structs::write<T: Copy>(cell: &mut generic_structs::Cell<T>, value: T) {
    owns cell.value;
    ensures cell.value == value;
} by { execute(); simp(); }

// The calls at `i32` use those contracts at `Cell<i32>`.
fn generic_structs::round_trip(x: i32) -> i32 {
    ensures result == x;
} by { execute(); simp(); }

// Two fields of `T` are two values: a swap exchanges them.
fn generic_structs::swap<T: Copy>(pair: &mut generic_structs::Pair<T>) {
    owns pair.first;
    owns pair.second;
    ensures pair.first == old(pair.second);
    ensures pair.second == old(pair.first);
} by { execute(); simp(); }

// The call at `u8` uses that contract at `Pair<u8>`.
fn generic_structs::swapped(x: u8, y: u8) -> u8 {
    ensures result == y;
} by { execute(); simp(); }
