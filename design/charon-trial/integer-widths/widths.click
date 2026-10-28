verifying "widths.rs";

// Each Rust integer width is the C integer of its width: `isize` and
// `usize` are the pinned target's 64 bits. Arithmetic that could overflow
// owes Rust's panic check: an explicit range check for the narrow widths,
// computed in `int`, and the kernel's signed-overflow check at `i32` and
// `i64`.

fn add64(a: u64, b: u64) -> u64 {
    requires a <= 1000u64 and b <= 1000u64;
    ensures result == a + b;
}

fn sub8(x: i8, y: i8) -> i8 {
    requires 0i8 <= x and x <= 100i8 and 0i8 <= y and y <= 100i8;
    ensures result as i32 == x as i32 - y as i32;
}

fn widen16(x: i16) -> i64 {
    ensures result == x as i64;
}

fn scale(x: i64) -> i64 {
    requires -1000i64 <= x and x <= 1000i64;
    ensures to_integer(result) == to_integer(x * 3i64 - 1i64);
}

fn diff(a: isize, b: isize) -> isize {
    requires 0isize <= a and a <= 1000isize and 0isize <= b and b <= 1000isize;
    ensures result == a - b;
}

fn narrow(x: u64) -> u8 {
    ensures result as u32 == (x as u32 & 255u32);
}

fn bump(x: &mut i16) {
    owns *x;
    requires *x < 100i16;
    ensures *x == old(*x) + 1i16;
}

fn lossless(x: u32) -> u64 {
    ensures result == x as u64;
}

fn signed_from(x: i8) -> i64 {
    ensures result == x as i64;
}

fn deposit(account: &mut Account, amount: i64) {
    owns *account;
    requires 0i64 <= account.balance and account.balance <= 1000000i64;
    requires 0i64 <= amount and amount <= 1000000i64;
    ensures account.balance == old(account.balance) + amount;
    ensures account.id == old(account.id);
}

fn value(amount: Amount) -> i64 {
    ensures result == match amount {
        Amount::Credit(x) => x as i64,
        Amount::Debit(x) => x,
    };
}

fn classify(x: i8) -> u8 {
    ensures x == 0i8 implies result == 0u8;
    ensures (x == 1i8 or x == 2i8) implies result == 1u8;
}

fn first(x: Option<u64>) -> u64 {
    ensures result == match x {
        Option::Some(v) => v,
        Option::None => 0u64,
    };
}

// A guard bounds the operand of a narrow unsigned addition: its panic check
// is `i <= 4294967295u32 - 1u32`, in the unsigned domain. The guard is a
// `bool` value, split where the `if` tests it; that fact has no source
// spelling for selected-premise arithmetic to cite, so the proof splits on
// the comparison itself.
fn step_below(i: u32, n: u32) -> u32 {
    ensures i < n implies result == i + 1u32;
    ensures i >= n implies result == i;
} by {
    if i < n { step_until(function.exit); solve(); }
    else { step_until(function.exit); solve(); }
}
