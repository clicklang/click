# A freed cell is not read through another owner after a loop

A use after free. `f` saves `h->ptr`, a loop swaps the pointers of two
holders once, `f` frees `g->ptr`, which is now the saved pointer, and then
reads through `saved`.

A view of the saved cell that outlived the loop, still attached to
`holder(h)`, would let the proof unfold `holder(g)`, free its cell and read
the freed memory through `holder(h)`. The verifier refuses the proof. Today
it refuses at the `free`: the cell `holder(h)` gives read authority for is
not shown separate from the allocation being freed.

That refusal is conservative. The two holders are separate owners, so the
cells they own are distinct, and a version of this function that did not read
`saved` would be correct C that is refused the same way.

```c filename=a_freed_cell_is_not_read_through_another_owner_after_a_loop.c
struct holder {
    int32* ptr;
};

int32 f(struct holder* h, struct holder* g) {
    int32* saved = h->ptr;
    int32* t = 0;
    int32 i = 0;
    while (i < 1) {
        t = h->ptr;
        h->ptr = g->ptr;
        g->ptr = t;
        i = i + 1;
    }
    free(g->ptr);
    return saved[0];
}
```

```click
resource holder(h: struct holder*) {
    owns h->ptr;
    owns allocation(h->ptr, 4);
    owns h->ptr[0..1];
}

verifying "a_freed_cell_is_not_read_through_another_owner_after_a_loop.c";

int32 f(struct holder* h, struct holder* g) {
    owns holder(h);
    consumes holder(g);
    produces g->ptr;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        owns holder(h);
        owns holder(g);
        initialize by simp;
        preserve by {
            unfold(holder(h));
            unfold(holder(g));
            step(); step(); step(); step();
            fold(holder(h));
            fold(holder(g));
            close_invariants();
        }
    }
    unfold(holder(g));
    step();
    step();
    simp();
}
```

```expect
fail: resource would remain usable after its allocation is freed
```
