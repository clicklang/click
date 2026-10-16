# Pointer reads before an address equality

Two nonvolatile pointer fields are read before the C branch establishes a
three-link chain between their source addresses. A C pointer comparison
states only that the addresses are equal (`(uint64)a == (uint64)b`), not that
the pointers are, so the trusted equality graph no longer relates the two
reads through it. The reads are of one cell, so `x == y` holds; proving it
needs load congruence over address equality, the follow-up recorded in
`design/pointer-subobject-extents.md` (Phase B).

This fixture pins the current refusal so that the follow-up turns it back
into a pass.

```c filename=late_pointer_load_equality.c
struct node { struct node *next; };

int32 equal_reads(struct node *a, struct node *b, struct node *c,
                  struct node *d) {
    struct node *x = a->next;
    struct node *y = d->next;
    if (a != b) return 1;
    if (c != d) return 1;
    if (b != c) return 1;
    return x == y;
}
```

```click
verifying "late_pointer_load_equality.c";

int32 equal_reads(struct node* a, struct node* b, struct node* c,
                  struct node* d) {
    views a->next;
    views d->next;
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    branch then {
        step();
        simp();
    } else {}
    branch then { step(); simp(); } else {}
    branch then { step(); simp(); } else {}
    have x == y;
    step();
    simp();
}
```

```expect
fail: could not establish `x == y`
```
