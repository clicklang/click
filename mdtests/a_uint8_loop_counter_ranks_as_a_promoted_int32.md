# A uint8 loop counter ranks as a promoted int32

C promotes a `uint8` operand to `int` before arithmetic, so `4 - x` over a
`uint8 x` is an `int32` expression, and the loop ranks in the int32 carrier
exactly as an `int32` counter would: the bundle owes `0 <= 4 - x` and
`3 - x < 4 - x` as signed comparisons at the entry value of `x`. Both close
from the guard `x < 4` and the promoted range `0 <= x`.

Compare `mdtests/an_unsigned_loop_counter_store_is_bounded_by_its_guard.md`,
where the counter is a `uint32`: there no promotion happens, so `4 - x` is a
`uint32` measure and ranks by unsigned order instead.

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
        initialize by { simp(); }
        preserve by {
            step();
            step();
            close_invariants by {
                both {
                    arithmetic() using {
                        0 <= at(statement(3).entry, x);
                        at(statement(3).entry, x) < 4;
                    }
                } and {
                    both {
                        arithmetic() using {
                            0 <= at(statement(3).entry, x);
                            at(statement(3).entry, x) < 4;
                        }
                    } and {
                        arithmetic() using {
                            0 <= at(statement(3).entry, x);
                            at(statement(3).entry, x) < 4;
                        }
                    }
                }
            }
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
