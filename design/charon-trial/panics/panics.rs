pub fn above_three(x: u32) -> u32 {
    assert!(x > 3);
    x - 4
}

pub fn with_message(x: u32) -> u32 {
    assert!(x > 3, "too small");
    x
}

pub fn formatted(x: u32) -> u32 {
    assert!(x > 3, "x was {}", x);
    x
}

pub fn nonzero(x: u32) -> u32 {
    if x == 0 {
        panic!("zero")
    }
    x
}

pub fn classify(x: u8) -> u8 {
    match x {
        0 => 10,
        1 => 20,
        _ => unreachable!(),
    }
}

pub fn first(xs: &[u8]) -> u8 {
    assert!(xs.len() > 0);
    xs[0]
}

pub fn unwrapped(o: Option<u32>) -> u32 {
    o.unwrap()
}

pub fn expected(o: Option<i64>) -> i64 {
    o.expect("a value")
}
