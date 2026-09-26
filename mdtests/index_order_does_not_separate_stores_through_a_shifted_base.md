# index order does not separate stores through a shifted base

`p` is `a + 1`, so `p[i]` is `a[i + 1]`, and under `i < j` that is `a[j]`
when `j == i + 1`. The index order `i < j` separates `a[i]` from `a[j]`, not
`p[i]` from `a[j]`: the two stores are spelled through different bases of
one object, and the second may overwrite the first. The order walk proving
`i < j` must not be taken for a proof that the addresses differ.

```c filename=index_order_does_not_separate_stores_through_a_shifted_base.c
void mark(int32 *a, int32 n, int32 i, int32 j) {
    int32 *p = a + 1;
    p[i] = 1;
    a[j] = 2;
}
```

```click
verifying "index_order_does_not_separate_stores_through_a_shifted_base.c";

void mark(int32 *a, int32 n, int32 i, int32 j) {
    requires 0 <= i;
    requires i < j;
    requires j < n;
    owns a[0..n];
    ensures a[i + 1] == 1;
} by {
    step();
    step();
    step();
    execute();
    simp();
}
```

```expect
fail: the store to `a[j]` may have written it. If `(i + 1)` and `j` differ
```
