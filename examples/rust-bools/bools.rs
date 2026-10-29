// Rust `bool` values (Stage 5 of `design/machine-integers.md`): a
// comparison, `!` or connective is the `Bool` it tests, with no path split,
// and a `bool` field of an enum or an `Option<bool>` is a `Bool`.

pub enum Light {
    On(bool),
    Off,
}

pub fn light_flag(l: Light) -> bool {
    match l {
        Light::On(b) => b,
        Light::Off => false,
    }
}

pub fn make_light(b: bool) -> Light {
    Light::On(b)
}

pub fn option_flag(o: Option<bool>) -> bool {
    match o {
        Some(b) => !b,
        None => true,
    }
}

pub fn less(a: i32, b: i32) -> bool {
    let c = a < b;
    c
}

pub fn in_range(x: i32) -> bool {
    x >= 0 && x < 10
}

pub fn differs(a: bool, b: bool) -> bool {
    a != b
}

pub fn neither(a: bool, b: bool) -> bool {
    !(a || b)
}

pub fn all_below(a: i32, b: i32, c: i32, limit: i32) -> bool {
    let x = a < limit;
    let y = b < limit;
    let z = c < limit;
    x && y && z
}
