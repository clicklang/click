# a non-strict index order does not keep an earlier store

The companion of
[`stores_to_ordered_indices_keep_each_other.md`](stores_to_ordered_indices_keep_each_other.md)
with `i <= j` in place of `i < j`. The two indices may be equal, so the store
to `a[j]` may overwrite `a[i]` and the earlier value is gone. The order walk
reads only the facts filed under each node; it must still carry each edge's
strictness exactly, and `i <= j` is not a strict path.

```c filename=a_non_strict_index_order_does_not_keep_an_earlier_store.c
void mark(int32 *a, int32 n, int32 i, int32 j) {
    a[i] = 1;
    a[j] = 2;
}
```

```click
verifying "a_non_strict_index_order_does_not_keep_an_earlier_store.c";

void mark(int32 *a, int32 n, int32 i, int32 j) {
    requires 0 <= i;
    requires i <= j;
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
fail: the store to `a[j]` may have written it. If `i` and `j` differ, state `i != j`
```
