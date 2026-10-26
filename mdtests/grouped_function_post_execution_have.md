# Grouped proof facts after execution

`have` can establish a pure fact after `step_until(function.exit)` reaches
function exit, on the one path of `identity` and in each arm of a `branch` at
the C `if` of `branch_value`. Its scoped pure proof may open an existential
assumption and provide existential witnesses without applying those
goal-specific steps to the other contract claims.

```c filename=grouped_post_have.c
int32 identity(int32 x) {
    return x;
}
```

```c filename=grouped_post_have_branch.c
int32 branch_value(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```c filename=grouped_current_have.c
int32 current_have(int32 x) {
    return x;
}
```

```click
verifying "grouped_post_have.c";
verifying "grouped_post_have_branch.c";
verifying "grouped_current_have.c";

int32 identity(int32 x) {
    requires exists (k: int32) { k == x };
    ensures result == x;
    ensures result_witness: exists (j: int32) { j == result };
    ensures chosen_witness: exists (j: int32) { j == x };
} by {
    step_until(function.exit);
    have exists (j: int32) { j == result } by {
        witness { j: result };
        solve();
    }
    have exists (j: int32) { j == x } by {
        obtain (k: int32) { k == x }
        witness { j: k };
        solve();
    }
}

int32 branch_value(int32 flag) {
    ensures result >= 0;
} by {
    branch {
        step_until(function.exit);
        have result >= 0;
    } else {
        step_until(function.exit);
        have result >= 0;
    }
}

int32 current_have(int32 x) {
    ensures exists (j: int32) { j == result };
} by {
    have exists (j: int32) { j == x } by {
        witness { j: x };
        solve();
    }
}
```

```expect
pass
```
