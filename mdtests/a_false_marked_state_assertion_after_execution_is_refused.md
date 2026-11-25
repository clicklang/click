# A false marked-state assertion after execution is refused

The entry value of `a[m]` stays unknown at function exit, so `close()` cannot
prove that it was 5.

```c filename=a_false_marked_state_assertion_after_execution_is_refused.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_false_marked_state_assertion_after_execution_is_refused.c";

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
    step_until(function.exit);
    have at(entry, a[m]) == at(entry, a[m]) by close();
    have at(entry, a[m]) == 5 by { close(); }
    close();
}
```

```expect
fail: `solve` failed
```
