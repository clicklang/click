// The Rust core methods of `i16`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `i16::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: int16, b: int16) -> int16 {
    if a <= b { a } else { b }
}

function max(a: int16, b: int16) -> int16 {
    if a <= b { b } else { a }
}

function wrapping_add(a: int16, b: int16) -> int16 {
    ((a as uint16) + (b as uint16)) as int16
}

function wrapping_sub(a: int16, b: int16) -> int16 {
    ((a as uint16) - (b as uint16)) as int16
}

function wrapping_mul(a: int16, b: int16) -> int16 {
    ((a as uint16) * (b as uint16)) as int16
}

function saturating_add(a: int16, b: int16) -> int16 {
    if to_integer(a) + to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) + to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) + (b as uint16)) as int16
        }
    }
}

function saturating_sub(a: int16, b: int16) -> int16 {
    if to_integer(a) - to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) - to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) - (b as uint16)) as int16
        }
    }
}

function checked_add(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) + (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}

function checked_sub(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) - (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}

function abs_diff(a: int16, b: int16) -> uint16 {
    if b <= a { ((a as uint16) - (b as uint16)) as uint16 } else { ((b as uint16) - (a as uint16)) as uint16 }
}

function unsigned_abs(a: int16) -> uint16 {
    if a < (0i64 as int16) { ((0u32 as uint16) - (a as uint16)) as uint16 } else { a as uint16 }
}
