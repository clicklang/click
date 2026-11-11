# A store at the last heap element keeps the first

`q[0] = 7; q[m - 1] = 1;` in an allocation of `m` ints with `2 <= m` writes
two different elements: `m - 1` is at least `1`, so the second store misses
`q[0]`, and the later read `int r = q[0];` is the `7`. The size and the last
index are symbolic; only the contract's bounds place `m - 1` off `0`. The
read declares `r`, so a transition lies between the store and the read.

The store keeps a cached element only on a stated disequality of the two
`int32` index words. With no proof body, the implicit tail sees the store
drop `q[0]`, proves `((m - 1) as int32) != 0` by arithmetic before the store,
and runs the store again. `click expand` writes that `have` before the
store's `step()`.

```c filename=a_store_at_the_last_heap_element_keeps_the_first.c
int read_first(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_store_at_the_last_heap_element_keeps_the_first.c";

int32 read_first(int32 m) {
    requires 2 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7;
}
```

```expect
pass
```
