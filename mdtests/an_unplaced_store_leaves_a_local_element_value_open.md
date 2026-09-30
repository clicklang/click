# an unplaced store leaves a local element value open

The value half of `mdtests/an_unplaced_store_keeps_a_local_array_initialized.md`.
Under `0 <= u < 2` the store `loc[u] = 7` writes `loc[0]` when `u == 0`, so
`result == 5` is false on that path. The element is initialized either way,
so this is an ordinary unclosed goal, not a read of uninitialized storage.

```c filename=an_unplaced_store_leaves_a_local_element_value_open.c
int32 may_hit(int32 u) {
    int32 loc[2];
    loc[0] = 5;
    loc[1] = 5;
    loc[u] = 7;
    return loc[0];
}
```

```click
verifying "an_unplaced_store_leaves_a_local_element_value_open.c";

int32 may_hit(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
