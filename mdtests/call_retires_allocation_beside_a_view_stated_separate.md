# A call retires a lent allocation beside a view stated separate

`box_release` lends `boxed(box)` to `box_destroy`, which frees `box->data`,
and keeps a view of `q[0..1]`. The precondition states that the first `4 * n` bytes
of the entry value of `box->data` are separate from the view. The call proof
uses `n == 1` to restrict that premise to the four bytes being retired and
uses the ownership partition to separate the box header from the view.

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
import click::separation;

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
    have contains(
        memory(((box->data as (void *)) as (uint8 *))[0..4 * n]),
        memory(((box->data as (void *)) as (uint8 *))[0..4])
    ) by { solve(); }
    apply(separation::contains_refl(memory(q[0..1])));
    apply(separation::separate_restrict(
        memory(((box->data as (void *)) as (uint8 *))[0..4 * n]),
        memory(q[0..1]),
        memory(((box->data as (void *)) as (uint8 *))[0..4]),
        memory(q[0..1])
    ));
    unfold(boxed(box));
    have separate(memory((box as (int32 *))[0..2]), memory(q[0..1])) by { known(); }
    fold(boxed(box));
    step() {
        requires separate(memory((box as (int32 *))[0..2]), memory(q[0..1])) by { known(); }
        requires separate(memory(((box->data as (void *)) as (uint8 *))[0..4]), memory(q[0..1])) by { known(); }
    }
}
```

```expect
pass
```
