# An unsigned loop counter's store is bounded by a variable guard

The variable-bound counterpart of
`mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`.
`for (uint32 x = 0u; x < n; x++)` stores `values[x]` under the guard
`x < n`, and `requires n <= 4u32` bounds the guard's bound. The unsigned
chain `x <u n <=u 4` gives `0 <= x` and `x < 4` in the body, so the store
is inside `values[0..4]`; without the requirement the same `step()` is
refused as a store outside the owned range
(`mdtests/an_unsigned_index_below_an_unbounded_variable_is_refused.md`).

`4 - x` over the `uint32` counter is a `uint32` measure, ranked by
unsigned order. The back-edge members are the invariant `x + 1 <=u n` and
the descent `(0 - x) + 3 <u (0 - x) + 4`, both at the entry value of `x`.
The closer proves the invariant from the guard. The descent needs
`x <u 4`, which is the guard composed with the requirement; the closer
looks up one exact fact per lemma and does not compose a chain, so the
proof states that fact and the closer does the rest.

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
            have at(statement(3).entry, x) < 4u32 by {
                apply(uint32_lt_le_transitive(at(statement(3).entry, x), n, 4u32)) using {
                    at(statement(3).entry, x) < n;
                    n <= 4u32;
                }
            }
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
