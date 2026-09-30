pub fn choose(x: i32) -> i32 {
    if x < 7 { x + 1 } else { 7 }
}
pub struct Pair { pub left: i32, pub right: i32 }
pub fn set_seven(value: &mut i32) {
    let child = &mut *value;
    *child = 7;
    *value += 1;
}
pub fn update(parent: &mut Pair) -> i32 {
    set_seven(&mut parent.left);
    parent.left
}

pub fn shared_field(parent: &mut Pair) -> i32 {
    let child = &parent.right;
    parent.left = 7;
    *child
}
