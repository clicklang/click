# an index ordered through an equal index keeps an earlier store

`i == m` and `m < j` put `i` below `j` only through the equality: no order
fact names `i` at all. The store to `a[j]` keeps the cell at `a[i]` because
the order walk reads the edges filed under every member of `i`'s
recorded-equality class, not just under `i`'s own spelling.

The second function states the equality the other way round, `m == i`, and
the third reaches `j` through a constant, `i == 2` and `3 <= j`: the walk
steps from `i` to the constant `2` along the equality and from `2` to the
larger written constant `3` along the `<=` connection between constants.

```c filename=an_index_ordered_through_an_equal_index_keeps_an_earlier_store.c
void through_equal(int32 *a, int32 n, int32 i, int32 j, int32 m) {
    a[i] = 1;
    a[j] = 2;
}

void through_reversed_equal(int32 *a, int32 n, int32 i, int32 j, int32 m) {
    a[i] = 1;
    a[j] = 2;
}

void through_constant(int32 *a, int32 n, int32 i, int32 j) {
    a[i] = 1;
    a[j] = 2;
}
```

```click
verifying "an_index_ordered_through_an_equal_index_keeps_an_earlier_store.c";

void through_equal(int32 *a, int32 n, int32 i, int32 j, int32 m) {
    requires 0 <= i;
    requires i == m;
    requires m < j;
    requires j < n;
    owns a[0..n];
    ensures a[i] == 1;
} by {
    step();
    step();
    execute();
    simp();
}

void through_reversed_equal(int32 *a, int32 n, int32 i, int32 j, int32 m) {
    requires 0 <= i;
    requires m == i;
    requires m < j;
    requires j < n;
    owns a[0..n];
    ensures a[i] == 1;
} by {
    step();
    step();
    execute();
    simp();
}

void through_constant(int32 *a, int32 n, int32 i, int32 j) {
    requires i == 2;
    requires 3 <= j;
    requires j < n;
    owns a[0..n];
    ensures a[i] == 1;
} by {
    step();
    step();
    execute();
    simp();
}
```

```expect
pass
```
