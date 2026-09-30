verifying "borrow.rs";

int32 choose(int32 x) {
    requires 0 <= x;
    ensures result == (if x < 7 { x + 1 } else { 7 });
} by {
    execute();
    simp();
}

void set_seven(int32* value) {
    owns value[0..1];
    ensures value[0] == 8;
} by {
    execute();
    simp();
}

int32 update(struct Pair* parent) {
    owns parent->left;
    owns parent->right;
    ensures parent->left == 8;
    ensures parent->right == old(parent->right);
    ensures result == 8;
} by {
    execute();
    simp();
}

int32 shared_field(struct Pair* parent) {
    owns parent->left;
    views parent->right;
    ensures parent->left == 7;
    ensures result == old(parent->right);
} by {
    execute();
    simp();
}
