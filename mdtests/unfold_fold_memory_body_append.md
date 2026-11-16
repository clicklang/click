# Ordinary unfolding retains the named fold equation

```c filename=unfold_fold_function_appends_last_cell.c
int32 prefix_sum_equation(int32 a[], int32 n) {
    return 0;
}
```

```click
verifying "unfold_fold_function_appends_last_cell.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

int32 prefix_sum_equation(int32 a[], int32 n) {
    requires 0 < n;
    views a[0..n];
    ensures icount(a, 0, n) == icount(a, 0, n - 1) + to_integer(a[n - 1]) by {
        step_until(function.exit);
        unfold(icount(a, 0, n));
        solve();
    }
}
```

```expect
pass
```
