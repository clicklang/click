# A claim true on only some paths of a split condition is refused

The negative of
[`a_condition_reaching_one_value_along_two_paths_splits_into_them.md`](a_condition_reaching_one_value_along_two_paths_splits_into_them.md).
`execute()` splits `x > 0 && y > 0` into its three paths and continues each.
The claim that the function returns `2` unless `y < 0` fails on the path where
both comparisons hold, which returns `1` with `y > 0`, and that path is an
ordinary unclosed goal.

```c filename=a_claim_true_on_some_paths_of_a_split_condition_is_refused.c
int32 both_positive(int32 x, int32 y) {
    int32 r;
    if (x > 0 && y > 0) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}
```

```click
verifying "a_claim_true_on_some_paths_of_a_split_condition_is_refused.c";

int32 both_positive(int32 x, int32 y) {
    ensures result == 2 or y < 0;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
