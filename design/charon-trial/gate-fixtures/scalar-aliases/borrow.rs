pub fn alias_update(parent: &mut i32) {
    let child = &mut *parent;
    let first = child;
    let last = first;
    *last = 7;
    *parent += 1;
}

pub fn alias_caller(value: &mut i32) {
    alias_update(value);
}
