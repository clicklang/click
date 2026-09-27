# an unordered store index may write a constant element

The negative next door to
`mdtests/order_bounds_place_a_store_off_a_constant_element.md`. Under
`0 <= u < 2` the store `a[u] = 7` writes `a[0]` when `u == 0`, so the order
facts do not put the two indices apart and `a[0]` is not known to keep its
value.

```c filename=an_unordered_store_index_may_write_a_constant_element.c
int32 may_write(int32* a, int32 u) {
    a[0] = 5;
    a[1] = 5;
    a[u] = 7;
    return a[0];
}
```

```click
verifying "an_unordered_store_index_may_write_a_constant_element.c";

int32 may_write(int32* a, int32 u) {
    requires 0 <= u;
    requires u < 2;
    consumes a[0..2];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
