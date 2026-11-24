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
    apply(click::separation::separate_adjacent_ranges(p as (int32 *), 0, 2, 4));
    have contains(memory(p->second), memory((&p->second)[0..1])) by { normalize(); }
    apply(click::separation::contains_refl(memory(p->first)));
    apply(click::separation::separate_restrict(memory(p->first), memory(p->second),
        memory(p->first), memory((&p->second)[0..1])));
    mark before_store;
    step();
    have separate(statement(0).footprint, memory((&p->second)[0..1])) by {
        normalize() using { at(before_store, separate(memory(p->first), memory((&p->second)[0..1]))); };
    }
    have exact(p->second) == old(exact(p->second)) by {
        preserve(memory((&p->second)[0..1]), statement(0));
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
