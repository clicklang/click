pub struct Cell<T> {
    pub value: T,
    pub count: u32,
}

pub fn make<T: Copy>(value: T) -> Cell<T> {
    Cell { value, count: 0 }
}

pub fn read<T: Copy>(cell: &Cell<T>) -> T {
    cell.value
}

pub fn write<T: Copy>(cell: &mut Cell<T>, value: T) {
    cell.value = value;
}

pub fn round_trip(x: i32) -> i32 {
    let mut cell = make(0);
    write(&mut cell, x);
    read(&cell)
}

pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

pub fn swap<T: Copy>(pair: &mut Pair<T>) {
    let first = pair.first;
    pair.first = pair.second;
    pair.second = first;
}

pub fn swapped(x: u8, y: u8) -> u8 {
    let mut pair = Pair { first: x, second: y };
    swap(&mut pair);
    pair.first
}

impl<T: Copy> Cell<T> {
    pub fn get(&self) -> T {
        self.value
    }

    pub fn set(&mut self, value: T) {
        self.value = value;
    }
}

pub fn via_methods(x: u32) -> u32 {
    let mut cell = make(0);
    cell.set(x);
    cell.get()
}

pub fn read_twice<U: Copy>(cell: &Cell<U>) -> U {
    let first = read(cell);
    let second = cell.get();
    let _ = first;
    second
}

pub fn twice_at(x: i32) -> i32 {
    let cell = make(x);
    read_twice(&cell)
}
