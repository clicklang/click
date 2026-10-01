# An unsigned index below a constant bound indexes a global array

The file-scope counterpart of
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.md`.
The C frontend checks a file-scope subscript as `x >= 0 && x < 4` before
the access, and the owned-footprint check reads the store in element
coordinates. With `uint32 x` both read the signed pair `0 <= x`, `x < 4`
filed beside the biased unsigned test; with `uint64 x` the check's
`x >= 0u` is true of every unsigned value and the pair is filed on the
index's low word.

```c filename=an_unsigned_index_below_a_constant_bound_indexes_a_global_array.c
int32 values[4];

int32 read_global(uint32 x) {
    int32 r;
    r = 0;
    if (x < 4u) {
        r = values[x];
    }
    return r;
}

void write_global(uint32 x) {
    if (x < 4u) {
        values[x] = 7;
    }
}

int32 read_global_wide(uint64 x) {
    int32 r;
    r = 0;
    if (x < 4u) {
        r = values[x];
    }
    return r;
}

void write_global_wide(uint64 x) {
    if (x < 4u) {
        values[x] = 7;
    }
}
```

```click
verifying "an_unsigned_index_below_a_constant_bound_indexes_a_global_array.c";

int32 read_global(uint32 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_global(uint32 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}

int32 read_global_wide(uint64 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_global_wide(uint64 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
pass
```
