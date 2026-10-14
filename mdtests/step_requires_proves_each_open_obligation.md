# a step's `requires` entries prove each obligation its fast path leaves open

Each precondition of `first` uses a pure function whose definition the fast
path does not unfold, so the call step leaves both open. One `requires` entry per
obligation proves it at the step's pre-state, and the step then runs with every
obligation stated exactly.

```c filename=step_requires_proves_each_open_obligation.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_proves_each_open_obligation.c";

function is_positive(value: int32) -> int32 { if value > 0 { 1 } else { 0 } }

int32 first(int32 x, int32 y) {
    requires is_positive(x) == 1 or is_positive(y) == 1;
    requires is_positive(y) == 1 or is_positive(x) == 1;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires is_positive(a) == 1 or is_positive(b) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; }
                }
                assumption();
            }
            requires is_positive(b) == 1 or is_positive(a) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; }
                }
                assumption();
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
