// The Rust core methods of `i32`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `i32::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: int32, b: int32) -> int32 {
    if a <= b { a } else { b }
}

function max(a: int32, b: int32) -> int32 {
    if a <= b { b } else { a }
}

function wrapping_add(a: int32, b: int32) -> int32 {
    ((a as uint32) + (b as uint32)) as int32
}

function wrapping_sub(a: int32, b: int32) -> int32 {
    ((a as uint32) - (b as uint32)) as int32
}

function wrapping_mul(a: int32, b: int32) -> int32 {
    ((a as uint32) * (b as uint32)) as int32
}

function saturating_add(a: int32, b: int32) -> int32 {
    if to_integer(a) + to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) + to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) + (b as uint32)) as int32
        }
    }
}

function saturating_sub(a: int32, b: int32) -> int32 {
    if to_integer(a) - to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) - to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) - (b as uint32)) as int32
        }
    }
}

function checked_add(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) + (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}

function checked_sub(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) - (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}

function abs_diff(a: int32, b: int32) -> uint32 {
    if b <= a { (a as uint32) - (b as uint32) } else { (b as uint32) - (a as uint32) }
}

function unsigned_abs(a: int32) -> uint32 {
    if a < (0i64 as int32) { 0u32 - (a as uint32) } else { a as uint32 }
}
