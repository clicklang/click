// The Rust core methods of `u32`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `u32::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: uint32, b: uint32) -> uint32 {
    if a <= b { a } else { b }
}

function max(a: uint32, b: uint32) -> uint32 {
    if a <= b { b } else { a }
}

function wrapping_add(a: uint32, b: uint32) -> uint32 {
    a + b
}

function wrapping_sub(a: uint32, b: uint32) -> uint32 {
    a - b
}

function wrapping_mul(a: uint32, b: uint32) -> uint32 {
    a * b
}

function saturating_add(a: uint32, b: uint32) -> uint32 {
    if to_integer(a) + to_integer(b) <= 4294967295 { a + b } else { 4294967295u32 }
}

function saturating_sub(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { 0u32 }
}

function checked_add(a: uint32, b: uint32) -> Option<uint32> {
    if to_integer(a) + to_integer(b) <= 4294967295 {
        Option<uint32>::Some(a + b)
    } else {
        Option<uint32>::None
    }
}

function checked_sub(a: uint32, b: uint32) -> Option<uint32> {
    if b <= a { Option<uint32>::Some(a - b) } else { Option<uint32>::None }
}

function abs_diff(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { b - a }
}
