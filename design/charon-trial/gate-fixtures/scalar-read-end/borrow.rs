pub fn read_before_reuse(parent: &mut i32) -> i32 {
    let child = &mut *parent;
    let alias = child;
    let value = *alias;
    *parent = 8;
    value
}

pub fn read_caller(parent: &mut i32) -> i32 {
    read_before_reuse(parent)
}
