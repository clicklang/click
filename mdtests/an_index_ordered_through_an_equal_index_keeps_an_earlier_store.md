# An explicitly derived index order keeps an earlier store

The proof derives `i < j` from the selected equality and order premises before
executing either store. The store checker uses that direct order fact; it does
not need to recover the earlier cell through a memory-history walk.

The three functions cover equality in both orientations and an order derived
through constants. Their C and contracts are unchanged.

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
    have i < j by { solve() using { i == m; m < j; }; }
    step();
    step();
}

void through_reversed_equal(int32 *a, int32 n, int32 i, int32 j, int32 m) {
    requires 0 <= i;
    requires m == i;
    requires m < j;
    requires j < n;
    owns a[0..n];
    ensures a[i] == 1;
} by {
    have i < j by { solve() using { m == i; m < j; }; }
    step();
    step();
}

void through_constant(int32 *a, int32 n, int32 i, int32 j) {
    requires i == 2;
    requires 3 <= j;
    requires j < n;
    owns a[0..n];
    ensures a[i] == 1;
} by {
    have i < j by { solve() using { i == 2; 3 <= j; }; }
    step();
    step();
}
```

```expect
pass
```
