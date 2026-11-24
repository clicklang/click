# A call writes through a folded owner beside a live view

The folded resource owns the left field. The call uses separation from the
neighboring view as an entry prerequisite, and the caller can still read the
view after the write.

```c filename=verified_call_folded_write_separation.c
struct pair {
    int left;
    int right;
};

void update_left(struct pair *p) {
    p->left = 7;
}

int read_after_update(struct pair *p) {
    update_left(p);
    return p->right;
}
```

```click
resource left_cell(p: struct pair*) {
    owns p->left;
}

verifying "verified_call_folded_write_separation.c";

void update_left(struct pair* p) {
    owns left_cell(p);
} by {
    unfold(left_cell(p));
    step();
    fold(left_cell(p));
}

int32 read_after_update(struct pair* p) {
    owns left_cell(p);
    views p->right;
    requires separate(memory(p->left), memory(p->right));
    ensures result == old(p->right);
} by {
    step() by { close(); }
}
```

```expect
pass
```
