# a known step prerequisite still accepts an explicit proof

An earlier have establishes one precondition. The step still generates both preconditions and accepts a proof entry for each.

```c filename=step_requires_proves_already_known_preconditions.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_proves_already_known_preconditions.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        have a > 0 or b > 0 by solve();
        step() {
            requires a > 0 or b > 0 by solve();
            requires b > 0 or a > 0 by solve();
        }
        step();
        solve();
    }
}
```

```expect
pass
```
