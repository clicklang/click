# Cases proves that the written alternatives are exhaustive

The held disjunction mentions `y`. The ordinary obligation for `cases`
uses `y == 1` to establish the alternatives before either arm is assumed.
Pure proofs, execution frontiers and completed execution use the same obligation.
An explicit `have` before a post-execution split is checked before that split.

```c filename=cases_obligation.c
int32 choose(int32 x, int32 y) { return x; }
int32 choose_after(int32 x, int32 y) { return x; }
int32 choose_explicit(int32 x, int32 y) { return x; }
```

```click
verifying "cases_obligation.c";

theorem nonnegative(x: int32, y: int32) {
    requires x == 0 or x == y;
    requires y == 1;
    ensures x >= 0 by {
        cases {
            x == 0 => { solve(); }
            x == 1 => { solve(); }
        }
    }
}

int32 choose(int32 x, int32 y) {
    requires x == 0 or x == y;
    requires y == 1;
    ensures result == 0 or result == 1;
} by {
    cases {
        x == 0 => { step_until(function.exit); solve(); }
        x == 1 => { step_until(function.exit); solve(); }
    }
}

int32 choose_after(int32 x, int32 y) {
    requires x == 0 or x == y;
    requires y == 1;
    ensures result == 0 or result == 1;
} by {
    step_until(function.exit);
    cases {
        result == 0 => { solve(); }
        result == 1 => { solve(); }
    }
}

int32 choose_explicit(int32 x, int32 y) {
    requires x == 0 or x == y;
    requires y == 1;
    ensures result == 0 or result == 1;
} by {
    step_until(function.exit);
    have x == 0 or x == 1 by {
        extract(x == 0 or x == 1);
        assumption();
    }
    cases {
        x == 0 => { solve(); }
        x == 1 => { solve(); }
    }
}
```

```expect
pass
```
