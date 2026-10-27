# A uint8 loop counter ranks as a promoted int32

C promotes a `uint8` operand to `int` for the increment and narrows the
stored result back to `uint8`. The Integer measure `4 - x` observes that
stored byte at each end of the iteration. The guard `x < 4` and the
promoted range `0 <= x` prove that the increment remains in range, so its
observation increases by one and the measure decreases by one.

Compare `mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`,
whose counter increments directly in `uint32`. Both measures use Integer
arithmetic.

```c filename=a_uint8_loop_counter_ranks_as_a_promoted_int32.c
void clear(int32* values) {
    for (uint8 x = 0; x < 4; x++) {
        values[x] = 0;
    }
}
```

```click
verifying "a_uint8_loop_counter_ranks_as_a_promoted_int32.c";

void clear(int32* values) {
    owns values[0..4];
} by {
    step();
    step();
    loop {
        decreases 4 - x;
        invariant x <= 4;
        owns values[0..4];
        initialize by { solve(); }
        preserve by {
            step();
            step();
            close_invariants() by {
                both {
                    solve() using {
                        0 <= at(region(3).entry, x);
                        at(region(3).entry, x) < 4;
                    };
                } and {
                    both {
                        solve() using {
                            0 <= at(region(3).entry, x);
                            at(region(3).entry, x) < 4;
                        };
                    } and {
                        solve() using {
                            0 <= at(region(3).entry, x);
                            at(region(3).entry, x) < 4;
                        };
                    }
                }
            }
        }
    }
}
```

```expect
pass
```
