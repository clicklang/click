// The Rust core methods of `i8`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `i8::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: int8, b: int8) -> int8 {
    if a <= b { a } else { b }
}

function max(a: int8, b: int8) -> int8 {
    if a <= b { b } else { a }
}

function wrapping_add(a: int8, b: int8) -> int8 {
    ((a as uint8) + (b as uint8)) as int8
}

function wrapping_sub(a: int8, b: int8) -> int8 {
    ((a as uint8) - (b as uint8)) as int8
}

function wrapping_mul(a: int8, b: int8) -> int8 {
    ((a as uint8) * (b as uint8)) as int8
}

function saturating_add(a: int8, b: int8) -> int8 {
    if to_integer(a) + to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) + to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) + (b as uint8)) as int8
        }
    }
}

function saturating_sub(a: int8, b: int8) -> int8 {
    if to_integer(a) - to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) - to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) - (b as uint8)) as int8
        }
    }
}

function checked_add(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) + (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}

function checked_sub(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) - (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}

function abs_diff(a: int8, b: int8) -> uint8 {
    if b <= a { ((a as uint8) - (b as uint8)) as uint8 } else { ((b as uint8) - (a as uint8)) as uint8 }
}

function unsigned_abs(a: int8) -> uint8 {
    if a < (0i64 as int8) { ((0u32 as uint8) - (a as uint8)) as uint8 } else { a as uint8 }
}
