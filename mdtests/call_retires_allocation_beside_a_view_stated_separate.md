# A call retires a lent allocation beside a view stated separate

`box_release` lends `boxed(box)` to `box_destroy`, which frees `box->data`,
and keeps a view of `q[0..1]`. The precondition states that the first `4 * n` bytes
of the entry value of `box->data` are separate from the view. The call proof
uses `n == 1` to establish separation from the four bytes being retired.

`call_frees_owned_allocation_beside_borrowed_view.md` checks the same result
using the checked borrow partition without the explicit premise.

```c filename=box.c
struct box {
    int32* data;
};

void box_destroy(struct box* box) {
    free(box->data);
}

void box_release(struct box* box, struct box* other, int32* q, int32 n) {
    box_destroy(box);
}
```

```click
resource boxed(box: struct box*) {
    owns *box;
    owns allocation(box->data, 4);
    owns box->data[0..1];
}

verifying "box.c";

void box_destroy(struct box* box) {
    consumes boxed(box);
    produces *box;
} by {
    unfold(boxed(box));
}

void box_release(struct box* box, struct box* other, int32* q, int32 n) {
    consumes boxed(box);
    produces *box;
    owns *other;
    views q[0..1];
    requires n == 1;
    requires separate(memory(((box->data as (void *)) as (uint8 *))[0..4 * n]), memory(q[0..1]));
} by {
    step() by { solve(); }
}
```

```expect
pass
```
