# A false `transport using` after execution is refused

The companion of `a_false_transport_using_between_execution_steps_is_refused.md`.
Written after `execute()`, the same false `transport using` is checked by the
same step and refused with the same reason.

```c filename=a_false_transport_using_after_execution_is_refused.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_false_transport_using_after_execution_is_refused.c";

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
    execute();
    have at(entry, a[m]) == at(entry, a[m]) by normalize();
    transport(
        at(entry, a[m]) == at(entry, a[m]),
        at(entry, a[m]) == 5
    ) using {
        at(entry, a[m]) == at(entry, a[m]);
        m != i;
    };
    simp();
}
```

```expect
fail: `transport using` found no frame evidence carrying its source fact to the target's state
```
