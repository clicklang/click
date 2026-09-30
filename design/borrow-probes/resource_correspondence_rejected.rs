//! Compile separately with each documented --cfg selection.
#![allow(dead_code)]

struct Pair {
    left: i32,
    right: i32,
}

#[cfg(parent_during_child)]
fn rejected() {
    let mut pair = Pair { left: 4, right: 9 };
    let parent = &mut pair;
    let child = &mut parent.left;
    parent.left = 8;
    *child = 7;
}

#[cfg(write_during_shared)]
fn rejected() {
    let mut pair = Pair { left: 4, right: 9 };
    let shared = &pair.left;
    pair.left = 8;
    assert_eq!(*shared, 4);
}

#[cfg(use_after_move)]
fn rejected() {
    let original = Pair { left: 4, right: 9 };
    let recipient = original;
    assert_eq!(original.left, recipient.left);
}

fn main() {
    rejected();
}
