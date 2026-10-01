# An unsigned loop counter's store is bounded by its guard

`for (uint32 x = 0u; x < 4u; x++)` stores `values[x]` under the guard
`x < 4u`, which files `0 <= x` and `x < 4` in the body, so the store is
inside `values[0..4]`. It used to be refused as a store with no `owns`
fact for the widened index.

`4 - x` over the `uint32` counter is a `uint32` measure under C's usual
arithmetic conversions, so the loop ranks by unsigned order: the bundle's
nonnegativity member is `true`, and its decrease member is the unsigned
comparison `3 - x <u 4 - x` of the two wrapped differences at the entry
value of `x`. Both it and the invariant member `x + 1 <=u 4` are true here,
but closing either needs unsigned order arithmetic over the counter, which
the closer does not do yet: it reads an unsigned comparison as a signed
order between sign-bit-flipped values, and a flipped `x + 1` is not related
to a flipped `x` (`bugs/unsigned-order-arithmetic-in-closers.md`). The
first open member, the invariant, is the refusal this test pins; it changes
to `pass` when that bug is fixed.

```c filename=an_unsigned_loop_counter_store_is_bounded_by_its_guard.c
void clear(int32* values) {
    for (uint32 x = 0u; x < 4u; x++) {
        values[x] = 0;
    }
}
```

```click
verifying "an_unsigned_loop_counter_store_is_bounded_by_its_guard.c";

void clear(int32* values) {
    owns values[0..4];
} by {
    step();
    step();
    loop {
        decreases 4 - x;
        invariant x <= 4u32;
        owns values[0..4];
        initialize by { simp(); }
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: `x <= 4u32` remained open; this loop declares `decreases`, so the bundle also has `0 <= 4 - x` at the back edge, `4 - x` decreases at the back edge
```
