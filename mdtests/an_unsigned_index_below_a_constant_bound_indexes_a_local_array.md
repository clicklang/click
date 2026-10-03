# An unsigned index below a constant bound indexes a local array

The automatic-storage counterpart of
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.md`.
Forming `values + x` for a local array checks the element index against the
block, and the store then needs `values[x]` inside it. Both read the range
`x < 4u` established, for a `uint32` and a `uint64` index; the read after
the store finds the cell it wrote.

```c filename=an_unsigned_index_below_a_constant_bound_indexes_a_local_array.c
int32 write_then_read(uint32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 7;
    if (x < 4u) {
        values[x] = 7;
        r = values[x];
    }
    return r;
}

int32 write_then_read_wide(uint64 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 7;
    if (x < 4u) {
        values[x] = 7;
        r = values[x];
    }
    return r;
}
```

```click
verifying "an_unsigned_index_below_a_constant_bound_indexes_a_local_array.c";

int32 write_then_read(uint32 x) {
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 write_then_read_wide(uint64 x) {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
