# Preserve carries an exact read across a separate store

Both reads name their written points. The footprint and selected resource
identify the cell whose value is preserved.

```c filename=preserve_exact_scalar_read.c
struct Pair {
    int64 first;
    int32 second;
};

void touch(struct Pair *p) { p->first = 1; }
```

```click
verifying "preserve_exact_scalar_read.c";

void touch(struct Pair* p) {
    owns p->first;
    owns p->second;
    ensures true;
} by {
    step();
    have separate(statement(0).footprint, memory(*(&p->second))) by solve();
    have exact(p->second) == old(exact(p->second)) by {
        preserve(memory(*(&p->second)), statement(0));
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
