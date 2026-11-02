verifying "signed.rs";

// Signed division and remainder truncate toward zero, as in C. Each owes
// Rust's panic checks: a nonzero divisor, and not `MIN / -1` or `MIN % -1`.
// At `i32` and `i64` these are the kernel's division checks; `i8` and `i16`
// are computed in `int`, where `MIN / -1` fits, so they owe an explicit
// check. Negation is `0 - x` with the subtraction's checks. Bitwise
// operations cannot overflow; at `i8` and `i16` they are not yet supported.

fn half(x: i32) -> i32 {
    ensures result == x / 2i32;
}

fn modulo(x: i64, y: i64) -> i64 {
    requires 0i64 <= x and 0i64 < y;
    ensures result == x % y;
}

fn quotient8(x: i8, y: i8) -> i8 {
    requires 0i8 <= x and 0i8 < y;
    ensures result == x / y;
} by {
    step_until(function.exit);
    have to_integer(y as i32) > 0 by { assumption(); }
    have to_integer(y as i32) != -1 by {
        intro();
        solve() using { to_integer(y as i32) > 0; to_integer(y as i32) == -1; };
    }
    have to_integer(y as i32) != 0 by {
        intro();
        solve() using { to_integer(y as i32) > 0; to_integer(y as i32) == 0; };
    }
    have (y as i32) != 0i32 and ((x as i32) != -2147483648i32 or (y as i32) != -1i32) by {
        assumption();
    }

}

fn remainder16(x: i16, y: i16) -> i16 {
    requires 0i16 <= x and 0i16 < y;
    ensures result == x % y;
} by {
    step_until(function.exit);
    have to_integer(y as i32) > 0 by { assumption(); }
    have to_integer(y as i32) != -1 by {
        intro();
        solve() using { to_integer(y as i32) > 0; to_integer(y as i32) == -1; };
    }
    have to_integer(y as i32) != 0 by {
        intro();
        solve() using { to_integer(y as i32) > 0; to_integer(y as i32) == 0; };
    }
    have (y as i32) != 0i32 and ((x as i32) != -2147483648i32 or (y as i32) != -1i32) by {
        assumption();
    }

}

fn negate(x: i16) -> i16 {
    requires -100i16 <= x and x <= 100i16;
    ensures result as i32 == 0i32 - x as i32;
}

fn negate32(x: i32) -> i32 {
    requires x != -2147483648i32;
    ensures result == 0i32 - x;
}

fn mask(x: i32, y: i32) -> i32 {
    ensures result == (x & y);
}

fn toggle(x: i32, y: i32) -> i32 {
    ensures result == (x ^ y);
}

fn either(x: isize, y: isize) -> isize {
    ensures result == (x | y);
}

fn complement(x: i64) -> i64 {
    ensures result == ~x;
}

fn split(total: &mut isize, parts: isize) {
    owns *total;
    requires 0isize <= *total and 0isize < parts;
    ensures *total == old(*total) / parts;
}

// A signed left shift wraps, as Rust's does: the bits are shifted as an
// unsigned word and reinterpreted at the operand's width. A right shift is
// arithmetic. Each owes Rust's panic check that the count is below the
// operand's width; for `i8` and `i16` that is narrower than C's own check.
fn shift_left(x: i32, n: u32) -> i32 {
    requires n < 32u32;
    ensures result == (x << n);
}

fn shift_right(x: i64, n: i32) -> i64 {
    requires 0i32 <= n and n < 64i32;
    ensures result == (x >> n);
}

fn shift_narrow(x: i8, n: u32) -> i8 {
    requires n < 8u32;
    ensures true;
}
