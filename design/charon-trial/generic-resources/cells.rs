pub struct Cell<T> {
    pub value: T,
    pub count: u32,
}

pub fn write<T: Copy>(cell: &mut Cell<T>, value: T) {
    cell.value = value;
}

pub fn read<T: Copy>(cell: &Cell<T>) -> T {
    cell.value
}

pub fn set_and_get(cell: &mut Cell<u32>, x: u32) -> u32 {
    write(cell, x);
    read(cell)
}
