pub struct Cell {
    value: u32,
}

pub fn boxed(x: u32) -> u32 {
    let mut b = Box::new(Cell { value: x });
    b.value = b.value + 1;
    b.value
}
