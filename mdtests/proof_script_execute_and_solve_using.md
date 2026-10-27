# explicit scripts step to exit before solve, and solve can restrict its premises

This checks the two script shapes from the proof-scripts concept page: a
whole-function proof that steps to function exit with
`step_until(function.exit)` before `solve()`, which runs no C, and a
`solve()` whose search is restricted to the facts listed in `using`.

```c filename=identity_value.c
int32 identity_value(int32 x) {
    return x;
}
```

```c filename=checked_index.c
int32 checked_index(int32 i, int32 n) {
    return i;
}
```

```click
verifying "identity_value.c";
verifying "checked_index.c";

int32 identity_value(int32 x) {
    ensures result == x by {
        step_until(function.exit);
        solve();
    }
}

int32 checked_index(int32 i, int32 n) {
    requires i >= 0;
    requires i < n;
    ensures in_range: 0 <= i and i < n and result == i by {
        step_until(function.exit);
        solve() using {
            i >= 0;
            i < n;
        };
    }
}
```

```expect
pass
```
