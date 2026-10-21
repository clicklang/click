pub struct Cell {
    value: u32,
}

pub fn boxed(x: u32) -> u32 {
    let mut b = Box::new(Cell { value: x });
    b.value = b.value + 1;
    b.value
}

pub fn make(x: u32) -> Box<Cell> {
    Box::new(Cell { value: x })
}

pub fn read(b: Box<Cell>) -> u32 {
    b.value
}

pub fn through(x: u32) -> u32 {
    let b = make(x);
    read(b)
}

pub fn maybe(x: u32, make: bool) -> Option<Box<Cell>> {
    if make {
        Some(Box::new(Cell { value: x }))
    } else {
        None
    }
}

pub fn value_or(o: Option<Box<Cell>>, d: u32) -> u32 {
    match o {
        Some(b) => b.value,
        None => d,
    }
}

pub fn maybe_through(x: u32, make: bool) -> u32 {
    value_or(maybe(x, make), 0)
}
