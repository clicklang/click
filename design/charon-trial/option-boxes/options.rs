pub struct Cell {
    value: u32,
}

pub fn maybe(x: u32, make: bool) -> u32 {
    let o = if make { Some(Box::new(Cell { value: x })) } else { None };
    match o {
        Some(b) => b.value,
        None => 0,
    }
}

pub fn dropped(x: u32, make: bool) -> u32 {
    let _o = if make { Some(Box::new(Cell { value: x })) } else { None };
    x
}
