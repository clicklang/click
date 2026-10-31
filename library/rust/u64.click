// The Rust core methods of `u64`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `u64::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: uint64, b: uint64) -> uint64 {
    if a <= b { a } else { b }
}

function max(a: uint64, b: uint64) -> uint64 {
    if a <= b { b } else { a }
}

function wrapping_add(a: uint64, b: uint64) -> uint64 {
    a + b
}

function wrapping_sub(a: uint64, b: uint64) -> uint64 {
    a - b
}

function wrapping_mul(a: uint64, b: uint64) -> uint64 {
    a * b
}

function saturating_add(a: uint64, b: uint64) -> uint64 {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 { a + b } else { 18446744073709551615u64 }
}

function saturating_sub(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { 0u64 }
}

function checked_add(a: uint64, b: uint64) -> Option<uint64> {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 {
        Option<uint64>::Some(a + b)
    } else {
        Option<uint64>::None
    }
}

function checked_sub(a: uint64, b: uint64) -> Option<uint64> {
    if b <= a { Option<uint64>::Some(a - b) } else { Option<uint64>::None }
}

function abs_diff(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { b - a }
}
