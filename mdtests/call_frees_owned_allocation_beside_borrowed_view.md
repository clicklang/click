# A call frees an owned allocation beside a separately borrowed view

`boxed(box)` owns every byte of the allocation that `box_destroy` frees.
The caller's `views q[0..1]` is backed by a separate checked borrow, so it cannot
alias those owned bytes in a valid entry partition. The proof opens the
composite to establish byte-range separation and supplies it to the call.
`call_rejects_lending_the_allocation_it_transfers.md` rejects a caller that
tries to supply the freed cell itself as this borrowed view.

```c filename=box.c
struct box {
    int32* data;
};

void box_destroy(struct box* box) {
    free(box->data);
}

void box_release(struct box* box, struct box* other, int32* q) {
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

void box_release(struct box* box, struct box* other, int32* q) {
    consumes boxed(box);
    produces *box;
    owns *other;
    views q[0..1];
} by {
    unfold(boxed(box));
    have separate(memory(((box->data as (void *)) as (uint8 *))[0..4]), memory(q[0..1])) by { solve(); }
    fold(boxed(box));
    step() by { known(); }
}
```

```expect
pass
```
