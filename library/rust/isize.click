// The Rust core methods of `isize`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `isize::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: int64, b: int64) -> int64 {
    if a <= b { a } else { b }
}

function max(a: int64, b: int64) -> int64 {
    if a <= b { b } else { a }
}

function wrapping_add(a: int64, b: int64) -> int64 {
    ((a as uint64) + (b as uint64)) as int64
}

function wrapping_sub(a: int64, b: int64) -> int64 {
    ((a as uint64) - (b as uint64)) as int64
}

function wrapping_mul(a: int64, b: int64) -> int64 {
    ((a as uint64) * (b as uint64)) as int64
}

function saturating_add(a: int64, b: int64) -> int64 {
    if to_integer(a) + to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) + to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) + (b as uint64)) as int64
        }
    }
}

function saturating_sub(a: int64, b: int64) -> int64 {
    if to_integer(a) - to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) - to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) - (b as uint64)) as int64
        }
    }
}

function checked_add(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) + (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}

function checked_sub(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) - (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}

function abs_diff(a: int64, b: int64) -> uint64 {
    if b <= a { (a as uint64) - (b as uint64) } else { (b as uint64) - (a as uint64) }
}

function unsigned_abs(a: int64) -> uint64 {
    if a < 0i64 { 0u64 - (a as uint64) } else { a as uint64 }
}
