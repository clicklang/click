pub fn peek<T: Copy>(value: &T) -> T {
    *value
}

pub fn put<T: Copy>(slot: &mut T, value: T) {
    *slot = value;
}

pub fn exchange<T: Copy>(left: &mut T, right: &mut T) {
    let held = *left;
    *left = *right;
    *right = held;
}

pub struct Slots {
    pub a: u32,
    pub b: u32,
}

pub fn use_refs(slots: &mut Slots) -> u32 {
    exchange(&mut slots.a, &mut slots.b);
    put(&mut slots.a, peek(&slots.b));
    slots.a
}
