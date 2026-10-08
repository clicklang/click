# An interface fact needs its terms defined in each arm

This is `bubble_pass3_max_suffix` without `have defined(j + 1)` in the arms.
Each arm proves `p[j] <= p[j + 1]`, and the join still refuses the interface:
a fact holds in an arm only together with what its terms need to denote a
value, and `p[j + 1]` needs `j + 1` not to overflow. The join proves that
from facts the arm already holds and does not search for it, so the arm has
to have stated it. The refusal says so.

```c filename=bubble_pass3.c
int32 bubble_pass3(int32 p[3]) {
    int32 j;
    int32 tmp;
    j = 0;
    while (j < 2) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    return 0;
}
```

```click
verifying "bubble_pass3.c";

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_pass3(int32 p[3]) {
    consumes p[0..3];
    ensures max_at_end: all_le_range(p, 0, 2, p[2]);
} by {
    step();
    step();
    step();
    loop {
        decreases 2 - j;
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            simp();
        }
        preserve by {
            branch ensuring {
                fact p[j] <= p[j + 1];
                fact all_le_range(p, 0, j, p[j + 1]);
            } then {
                step();
                step();
                step();
                have p[j] <= p[j + 1];
                have all_le_range(p, 0, j, p[j + 1]) by {
                    unfold(all_le_range);
                    simp();
                }
            } else {
                have p[j] <= p[j + 1];
                have all_le_range(p, 0, j, p[j + 1]) by {
                    unfold(all_le_range);
                    simp();
                }
            }
            step();
            unfold(all_le_range);
            close_invariants();
        }
        owns p[0..3];
    }
    step();
    unfold(all_le_range);
    simp();
}
```

```expect
fail: the then arm holds the interface fact `p[j] <= p[(j + 1)]` but not what its terms need to denote a value
```
