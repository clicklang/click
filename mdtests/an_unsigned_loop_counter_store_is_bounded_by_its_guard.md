# An unsigned loop counter's store is bounded by its guard

`for (uint32 x = 0u; x < 4u; x++)` stores `values[x]` under the guard
`x < 4u`, which files `0 <= x` and `x < 4` in the body, so the store is
inside `values[0..4]`. It used to be refused as a store with no `owns`
fact for the widened index.

The measure `4 - x` is an Integer difference. The guard bounds the
`uint32` increment below its wrap point, so its observation increases by
one. The closer proves the invariant `x + 1 <=u 4`, the Integer measure's
nonnegativity, and its descent from that guard.

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
        initialize by { solve(); }
        preserve by {
            step();
            step();
        }
    }
}
```

```expect
pass
```
