# an unplaced store does not initialize an element beyond it

`loc[u] = 7` under `0 <= u < 2` forgets the values of `loc[0]` and `loc[1]`
but keeps them initialized; `loc[2]` was never written by any store, so
reading it stays a read of uninitialized storage. See
`mdtests/an_unplaced_store_keeps_a_local_array_initialized.md`.

```c filename=an_unplaced_store_does_not_initialize_an_element_beyond_it.c
int32 beyond(int32 u) {
    int32 loc[3];
    loc[0] = 5;
    loc[1] = 5;
    loc[u] = 7;
    return loc[2];
}
```

```click
verifying "an_unplaced_store_does_not_initialize_an_element_beyond_it.c";

int32 beyond(int32 u) {
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
