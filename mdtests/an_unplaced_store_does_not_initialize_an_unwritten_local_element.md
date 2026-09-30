# an unplaced store does not initialize an unwritten local element

The negative next door to
`mdtests/an_unplaced_store_keeps_a_local_array_initialized.md`. The
initialization record keeps the bytes a forgotten cell held, and only those:
`loc[u] = 7` under `0 <= u < 2` writes `loc[1]` only when `u == 1`, so after
it `loc[1]` may still be the never-written element, and reading it is a read
of uninitialized storage. The same holds for an element beyond every store
the facts allow.

```c filename=an_unplaced_store_does_not_initialize_an_unwritten_local_element.c
int32 unwritten_neighbour(int32 u) {
    int32 loc[2];
    loc[0] = 5;
    loc[u] = 7;
    return loc[1];
}
```

```click
verifying "an_unplaced_store_does_not_initialize_an_unwritten_local_element.c";

int32 unwritten_neighbour(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
