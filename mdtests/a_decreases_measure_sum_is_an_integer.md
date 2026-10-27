# A decreases measure sum is an Integer

The Integer fact about the sum closes the same measure member on both
entry paths of the disjunctive guard. The second function allows the
measure to exceed `int32` without a proof-only bound on its sum.

```c filename=integer_measure.c
int32 enters_either_way(int32 a, int32 b) {
    while (a > 0 || b > 0) {
        a = 0;
        b = 0;
    }
    return a + b;
}

int32 count_down(int32 a, int32 b) {
    while (a > 0) {
        a = a - 1;
    }
    return a;
}
```

```click
verifying "integer_measure.c";

int32 enters_either_way(int32 a, int32 b) {
    requires a >= 0;
    requires a <= 1;
    requires b >= 0;
    requires b <= 1;
    ensures result == 0;
} by {
    loop {
        decreases a + b;
        invariant a >= 0;
        invariant a <= 1;
        invariant b >= 0;
        invariant b <= 1;
        preserve by {
            have 0 < a + b by {
                cases {
                    a > 0 => {
                        solve() using { a > 0; b >= 0; a <= 1; b <= 1; };
                    }
                    b > 0 => {
                        solve() using { b > 0; a >= 0; a <= 1; b <= 1; };
                    }
                }
            }
            step();
            step();
            close_invariants();
        }
    }
    step();
    solve();
}

int32 count_down(int32 a, int32 b) {
    requires a >= 0;
    requires b >= 0;
    ensures result == 0;
} by {
    loop {
        decreases a + b;
        invariant a >= 0;
        invariant b >= 0;
    }
}
```

```expect
pass
```
