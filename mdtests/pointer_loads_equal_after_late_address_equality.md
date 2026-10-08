# Pointer reads before an address equality

Two nonvolatile pointer fields are read before the C branch establishes a
three-link chain between their source addresses. The already-read values then
have one `simp()` proof of equality through the trusted equality graph.

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
    have x == y by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
