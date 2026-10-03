pub fn rejected(slot: &mut u16) {
    let child = &mut *slot;
    *slot = 9;
    *child = 1;
}
