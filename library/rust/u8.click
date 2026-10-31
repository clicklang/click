// The Rust core methods of `u8`, as specification functions. A call to
// one of these methods in imported Rust is a call to an external function
// whose contract states its result with the function of the same name here,
// so a proof reads `u8::min(a, b)` as the code does. Each is opaque until
// a proof unfolds it. The library defines the same functions for every
// integer type; a signed type's wrapping and unsigned results are its values
// as the unsigned type of its width, which a cast converts modularly.

function min(a: uint8, b: uint8) -> uint8 {
    if a <= b { a } else { b }
}

function max(a: uint8, b: uint8) -> uint8 {
    if a <= b { b } else { a }
}

function wrapping_add(a: uint8, b: uint8) -> uint8 {
    (a + b) as uint8
}

function wrapping_sub(a: uint8, b: uint8) -> uint8 {
    (a - b) as uint8
}

function wrapping_mul(a: uint8, b: uint8) -> uint8 {
    (a * b) as uint8
}

function saturating_add(a: uint8, b: uint8) -> uint8 {
    if to_integer(a) + to_integer(b) <= 255 { (a + b) as uint8 } else { (255u32 as uint8) }
}

function saturating_sub(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (0u32 as uint8) }
}

function checked_add(a: uint8, b: uint8) -> Option<uint8> {
    if to_integer(a) + to_integer(b) <= 255 {
        Option<uint8>::Some((a + b) as uint8)
    } else {
        Option<uint8>::None
    }
}

function checked_sub(a: uint8, b: uint8) -> Option<uint8> {
    if b <= a { Option<uint8>::Some((a - b) as uint8) } else { Option<uint8>::None }
}

function abs_diff(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (b - a) as uint8 }
}
