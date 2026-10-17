# A `transport using` after execution carries a distinct cell

The companion of `a_distinct_symbolic_cell_survives_a_store.md`, which writes
the same `transport using` between execution steps. Written after
`execute()`, it carries the entry read of `a[m]` past the store to `a[i]` from
the same listed premises, so the tactic means the same thing in both places.

```c filename=a_transport_using_after_execution_carries_a_distinct_cell.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_transport_using_after_execution_carries_a_distinct_cell.c";

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
        at(entry, a[m]) == a[m]
    ) using {
        at(entry, a[m]) == at(entry, a[m]);
        m != i;
    };
    simp();
}
```

```expect
pass
```
