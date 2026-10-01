# An unsigned loop counter's store is bounded by a variable guard

The variable-bound counterpart of
`mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`.
`for (uint32 x = 0u; x < n; x++)` stores `values[x]` under the guard
`x < n`, and `requires n <= 4u32` bounds the guard's bound. The unsigned
chain `x <u n <=u 4` gives `0 <= x` and `x < 4` in the body, so the store
is inside `values[0..4]`; without the requirement the same `step()` is
refused as a store outside the owned range
(`mdtests/an_unsigned_index_below_an_unbounded_variable_is_refused.md`).

The loop still does not verify: a ranking measure must be an `int32`
expression, and `4 - x` over the `uint32` counter is not one. That is the
refusal this test pins, after the body's store, increment, and invariant
have been checked; it changes when unsigned measures are supported.

```c filename=an_unsigned_loop_counter_store_is_bounded_by_a_variable_guard.c
void clear(int32* values, uint32 n) {
    for (uint32 x = 0u; x < n; x++) {
        values[x] = 0;
    }
}
```

```click
verifying "an_unsigned_loop_counter_store_is_bounded_by_a_variable_guard.c";

void clear(int32* values, uint32 n) {
    requires n <= 4u32;
    owns values[0..4];
} by {
    step();
    step();
    loop {
        decreases 4 - x;
        invariant x <= n;
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
fail: termination measure variable `x` does not hold an int32 value
```
