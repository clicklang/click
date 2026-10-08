# C reads through an owned resource inside a loop

`count` holds `flat(p)` folded across a loop whose guard reads `p->value`.
The loop declares the resource, so its body holds it at a new occurrence; the
read authority for the memory the resource owns directly is derived again at
the loop head from the resource's definition, and the guard reads through it.
No `unfold` is written.

`a_pointer_saved_before_a_loop_is_not_read_through_the_owner_after_it.md` is
the case where deriving it again matters.

```c filename=c_reads_through_an_owned_resource_inside_a_loop.c
struct cell {
    int32 value;
    int32 other;
};

int32 count(struct cell* p) {
    int32 i = 0;
    while (i < p->value) {
        i = i + 1;
    }
    return i;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "c_reads_through_an_owned_resource_inside_a_loop.c";

int32 count(struct cell* p) {
    owns flat(p);
    requires p->value <= 100;
} by {
    step();
    step();
    loop as counting {
        decreases p->value - i;
        invariant i >= 0;
        owns flat(p);

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
