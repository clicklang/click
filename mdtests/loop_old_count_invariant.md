# loop invariant lowers old-state stdlib count

This checks that `old(...)` in a loop invariant re-elaborates its body in the
entry-state spec context. In particular, `old(permutation::count(...))` reaches the stdlib
`count` function and keeps its `.fold` as pure spec/core over entry memory.

```c filename=loop_old_count_invariant.c
int32 loop_old_count_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
import click::permutation;

verifying "loop_old_count_invariant.c";

int32 loop_old_count_invariant(int32 p[3]) {
    requires viewable(p[0..3]);
    ensures result_value: result == 3;
} by {
    step();
    step();
    loop {
        decreases (3 - i);
        invariant i >= 0 and i <= 3;
        invariant old(permutation::count(p, 0, 3, p[0])) == old(permutation::count(p, 0, 3, p[0]));
        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have old(permutation::count(p, 0, 3, p[0])) == old(permutation::count(p, 0, 3, p[0])) by {
                normalize();
            }
        }
        preserve by {
            mark iteration;
            step();
            have i >= 0 and i <= 3 by {
                both {
                    have at(region(3).entry, i) >= at(region(3).entry, 0);
                    solve() using { at(region(3).entry, i) >= at(region(3).entry, 0); at(region(3).entry, i) < at(region(3).entry, 3); };
                } and {
                    solve() using { at(region(3).entry, i) < at(region(3).entry, 3); };
                }
            }
        }
    }
    step();
    have result == 3 by {
        solve() using {
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
        };
    }
    known();
}
```

```expect
pass
```
