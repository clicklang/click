# A store preserves a cell with a distinct index

The companion of `store_does_not_preserve_a_symbolic_cell.md`: `elements`
turns `m != i` into cell separation, and `preserve` carries the selected
read across the write. Without the index inequality, this chain cannot close.

```c filename=a_distinct_symbolic_cell_survives_a_store.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_distinct_symbolic_cell_survives_a_store.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
} by {
    mark entry;
    step();
    have separate(memory(a[i]), memory(a[m])) by {
        apply(click::separation::elements(a, i, m)) using { m != i; };
    }
    have separate(statement(0).footprint, memory(a[m])) by {
        normalize() using { separate(memory(a[i]), memory(a[m])); };
    }
    have a[m] == at(entry, a[m]) by {
        preserve(separate(statement(0).footprint, memory(a[m])));
    }
}
```

```expect
pass
```
