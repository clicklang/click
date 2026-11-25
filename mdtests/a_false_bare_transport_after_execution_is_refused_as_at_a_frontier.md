# A false bare `transport` after execution is refused as at a frontier

A bare `transport` at function exit uses the same proof search as at a
statement frontier. A reflexive equality supplies no proof of the target
value.

```c filename=a_false_bare_transport_after_execution_is_refused_as_at_a_frontier.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_false_bare_transport_after_execution_is_refused_as_at_a_frontier.c";

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
    transport(at(entry, a[m]) == at(entry, a[m]), at(entry, a[m]) == 5);
    close();
}
```

```expect
fail: `transport` found no checked proof from its source
```
