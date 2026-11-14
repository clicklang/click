# Explicit preservation after execution carries a distinct cell

The companion of `a_distinct_symbolic_cell_survives_a_store.md` applies the
same separation and preservation rules at function exit.

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
    step_until(function.exit);
    have separate(memory(a[i]), memory(a[m])) by {
        apply(click::separation::elements(a, i, m)) using { m != i; };
    }
    have separate(statement(0).footprint, memory(a[m])) by {
        normalize() using { separate(memory(a[i]), memory(a[m])); };
    }
    have a[m] == at(entry, a[m]) by {
        preserve(separate(statement(0).footprint, memory(a[m])));
    }
    solve();
}
```

```expect
pass
```
