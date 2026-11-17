pub fn bump(value: &mut i32) {
    *value += 1;
}

pub fn bump_through_child(parent: &mut i32) {
    let child = &mut *parent;
    bump(child);
    *child += 1;
    *parent += 1;
}
