// The Rust core methods of `u16`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `u16::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: uint16, b: uint16) -> uint16 {
    if a <= b { a } else { b }
}

function max(a: uint16, b: uint16) -> uint16 {
    if a <= b { b } else { a }
}

function wrapping_add(a: uint16, b: uint16) -> uint16 {
    (a + b) as uint16
}

function wrapping_sub(a: uint16, b: uint16) -> uint16 {
    (a - b) as uint16
}

function wrapping_mul(a: uint16, b: uint16) -> uint16 {
    (a * b) as uint16
}

function saturating_add(a: uint16, b: uint16) -> uint16 {
    if to_integer(a) + to_integer(b) <= 65535 { (a + b) as uint16 } else { (65535u32 as uint16) }
}

function saturating_sub(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (0u32 as uint16) }
}

function checked_add(a: uint16, b: uint16) -> Option<uint16> {
    if to_integer(a) + to_integer(b) <= 65535 {
        Option<uint16>::Some((a + b) as uint16)
    } else {
        Option<uint16>::None
    }
}

function checked_sub(a: uint16, b: uint16) -> Option<uint16> {
    if b <= a { Option<uint16>::Some((a - b) as uint16) } else { Option<uint16>::None }
}

function abs_diff(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (b - a) as uint16 }
}
