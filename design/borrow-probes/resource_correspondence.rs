//! Compiler/runtime witnesses for the resource correspondence design.
//! These are ordinary Rust tests, not Click proofs.

struct Pair {
    left: i32,
    right: i32,
}

fn set_seven(value: &mut i32) {
    let child = &mut *value;
    *child = 7;
    // The child is no longer used; its local storage need not have ended.
    *value += 1;
}

#[test]
fn exclusive_reborrow_returns_updated_field_and_preserves_neighbor() {
    let mut pair = Pair { left: 4, right: 9 };
    let parent = &mut pair;
    set_seven(&mut parent.left);
    assert_eq!(parent.left, 8);
    assert_eq!(parent.right, 9);
    parent.left = 10;
    assert_eq!((pair.left, pair.right), (10, 9));
}

#[test]
fn shared_borrow_preserves_field_until_parent_reuse() {
    let mut pair = Pair { left: 4, right: 9 };
    let parent = &mut pair;
    let shared = &parent.left;
    parent.right = 12;
    assert_eq!(*shared, 4);
    parent.left = 8;
    assert_eq!((pair.left, pair.right), (8, 12));
}

#[test]
fn disjoint_exclusive_fields_can_be_used_together() {
    let mut pair = Pair { left: 4, right: 9 };
    let left = &mut pair.left;
    let right = &mut pair.right;
    *left = 8;
    *right = 12;
    assert_eq!((*left, *right), (8, 12));
    assert_eq!((pair.left, pair.right), (8, 12));
}

#[test]
fn move_transfers_noncopy_value() {
    let original = Pair { left: 4, right: 9 };
    let mut recipient = original;
    recipient.left = 8;
    assert_eq!((recipient.left, recipient.right), (8, 9));
}
