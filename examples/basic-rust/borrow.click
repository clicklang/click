verifying "borrow.rs";

fn choose(x: i32) -> i32 {
    requires 0 <= x;
    ensures result == (if x < 7 { x + 1 } else { 7 });
} by {
    execute();
    simp();
}

fn set_seven(value: &mut i32) {
    owns *value;
    ensures *value == 8;
} by {
    execute();
    simp();
}

fn update(parent: &mut Pair) -> i32 {
    owns parent.left;
    owns parent.right;
    ensures parent.left == 8;
    ensures parent.right == old(parent.right);
    ensures result == 8;
} by {
    execute();
    simp();
}

fn shared_field(parent: &mut Pair) -> i32 {
    owns parent.left;
    views parent.right;
    ensures parent.left == 7;
    ensures result == old(parent.right);
} by {
    execute();
    simp();
}
