# A call cannot lend the field its folded input owns for writing

Passing the left field as the view would borrow the same bytes the call
receives through its folded owner.

```c filename=folded_write_overlap.c
struct pair {
    int left;
    int right;
};

void update_left_beside_view(struct pair *p, const int *q);

void alias_left(struct pair *p) {
    update_left_beside_view(p, &p->left);
}
```

```click
resource left_cell(p: struct pair*) {
    owns p->left;
}

verifying "folded_write_overlap.c";

extern void update_left_beside_view(struct pair* p, const int32* q) {
    owns left_cell(p);
    views q[0..1];
}

void alias_left(struct pair* p) {
    owns left_cell(p);
}
```

```expect
fail: stable-view this resource shape is outside stable-view support refused during planning
```
