# An unsigned loop counter's store is bounded by its guard

`for (uint32 x = 0u; x < 4u; x++)` stores `values[x]` under the guard
`x < 4u`, which files `0 <= x` and `x < 4` in the body, so the store is
inside `values[0..4]`. It used to be refused as a store with no `owns`
fact for the widened index.

The loop still does not verify: a ranking measure must be an `int32`
expression, and `4 - x` over the `uint32` counter is not one. That is the
refusal this test pins, after the body's store and increment have been
checked; it changes when unsigned measures are supported.

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
fail: termination measure variable `x` does not hold an int32 value
```
