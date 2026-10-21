pub fn peek(value: &u32) -> u32 {
    *value
}

pub fn put(slot: &mut u32, value: u32) {
    *slot = value;
}

pub fn exchange(left: &mut u32, right: &mut u32) {
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
