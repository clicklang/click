# compare_swap2 proves the stdlib two-cell permutation

This checks that a conditional swap can prove the output pair is a permutation
of the entry-state pair using the standard `permutation` predicate.

```c filename=compare_swap2_permutation.c
int32 compare_swap2_permutation(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    }
    return 0;
}
```

```click
import click::permutation;

verifying "compare_swap2_permutation.c";

int32 compare_swap2_permutation(int32 p[2]) {
    consumes p[0..2];
    ensures pair_permutation: permutation::permutation(p, old(p), 0, 2) by {
        step();
        if at(region(1).entry, p[1]) < at(region(1).entry, p[0]) {
            step_until(function.exit);
            unfold(permutation::permutation(p, old(p), 0, 2));
            intro() {
                unfold(permutation::count(p, 0, 2, x));
                unfold(permutation::count(old(p), 0, 2, x));
                have (0 + (if old(p[1]) == x { 1 } else { 0 }) + (if old(p[0]) == x { 1 } else { 0 })) == (0 + (if old(p[0]) == x { 1 } else { 0 }) + (if old(p[1]) == x { 1 } else { 0 })) by {
                    apply(permutation::two_indicator_counts_commute(
                        if old(p[1]) == x { true } else { false },
                        if old(p[0]) == x { true } else { false }
                    ));
                    close();
                }
                close();
            }
        } else {
            step_until(function.exit);
            unfold(permutation::permutation(p, old(p), 0, 2));
            intro() {
                close();
            }
        }
    }
}
```

```expect
pass
```
