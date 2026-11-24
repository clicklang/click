# The joined exit says which conjunct failed

The `otherwise` proof establishes `a == 0 or p[0] == 0` from the two
ways that `while (a != 0 && p[0] != 0)` can test false. After the loop,
the `then` arm knows that `a` is nonzero, so the first disjunct is
refuted and the returned `p[0]` must be zero.

The loop terminates because the body zeroes `a`, so `a` is the measure. Its
decrease obligation is `0 < a` at the head, which the first guard conjunct
gives only as `a != 0`; the arithmetic members are affine, so the preservation
body turns the disequality into `a > 0` by ruling out `a == 0` against that
conjunct before the step runs.

```c filename=loop_conjunctive_guard_exit_join.c
int32 uses_exit_disjunction(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    if (a != 0)
        return p[0];
    return 0;
}
```

```click
verifying "loop_conjunctive_guard_exit_join.c";

int32 uses_exit_disjunction(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result == 0;
} by {
    loop {
        decreases a;
        invariant a >= 0;
        invariant a <= 10;

        initialize by close();
        maintain by {
            have a > 0 by {
                if a > 0 {
                    close();
                } else {
                    have a == 0;
                    contradiction(a == 0);
                }
            }
            step();
        }
        otherwise {
            have a == 0 or p[0] == 0 by close();
        }
    }
    branch {
        true => {
            have p[0] == 0 by {
                cases {
                    a == 0 => {
                        have a == 0 by {
                            close();
                        }
                        contradiction(a == 0);
                    }
                    p[0] == 0 => {
                        close();
                    }
                }
            }
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}
```

```expect
pass
```
