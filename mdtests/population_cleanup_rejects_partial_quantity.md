# Cleanup requires the requested quantity to be the whole population

A live control records zero contributions and three remaining members. Spending
only two leaves one member and cannot restore the zero-contribution equation.
Partial batches are supported; retaining this cleanup control with mismatched
accounting is rejected. The C source is unchanged.

```c filename=partial_cleanup.c
struct counter { unsigned int value; };
unsigned int cleanup(struct counter* p) { p->value = 0u; return p->value; }
```

```click resource_semantics=authority
verifying "partial_cleanup.c";
resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact p->value == 3 - count(remaining(p));
}
uint32 cleanup(struct counter* p) {
    owns p->value;
    owns authority(remaining(p));
    requires count(remaining(p)) == 0;
} by {
    step();
    fold(3 of remaining(p));
    fold(control(p));
    open(control(p)) { unfold(2 of remaining(p)); }
    step();
    simp();
}
```

```expect
fail: Requires p->value == (3 - count(remaining(p)))
```
