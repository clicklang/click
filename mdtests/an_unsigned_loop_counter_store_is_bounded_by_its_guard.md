# An unsigned loop counter's store is bounded by its guard

`for (uint32 x = 0u; x < 4u; x++)` stores `values[x]` under the guard
`x < 4u`, which files `0 <= x` and `x < 4` in the body, so the store is
inside `values[0..4]`. It used to be refused as a store with no `owns`
fact for the widened index.

`4 - x` over the `uint32` counter is a `uint32` measure under C's usual
arithmetic conversions, so the loop ranks by unsigned order: the bundle's
nonnegativity member is `true`, and its decrease member is the unsigned
comparison `3 - x <u 4 - x` of the two wrapped differences at the entry
value of `x`, which the loop evaluates to `(0 - x) + 3 <u (0 - x) + 4`.

The closer proves both back-edge members from the guard with the `uint32`
order lemmas: the invariant `x + 1 <=u 4` and the descent.

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
pass
```
