# A `have` whose body misses between execution steps is refused

The companion of `a_have_whose_body_misses_after_execution_is_refused.md`. The
same written `have`, whose script cannot prove its proposition, is refused
with the same reason between execution steps and after execution: both run
the one checked `have` and report the script step that failed.

```c filename=a_have_whose_body_misses_between_execution_steps_is_refused.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_have_whose_body_misses_between_execution_steps_is_refused.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    step();
    have a[m] == 7 by {
        normalize();
    }
    execute();
    simp();
}
```

```expect
fail: `normalize` goal did not normalize to true
```
