# A narrow unsigned index below a constant bound indexes a global array

The `uint8` and `uint16` counterparts of
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_global_array.md`.
A narrow unsigned value is promoted to `int32` before it is compared or
used as an index, and the promotion files its range (`0 <= x` and
`x <= 255` for `uint8`, `x <= 65535` for `uint16`) as a path fact. The
file-scope subscript check `x >= 0 && x < 4` and the owned-footprint check
of the store read that lower bound beside the source's `x < 4`, as they do
for a parameter or local array. The source's own `0 <= x` is decided by the
same range, so it adds nothing.

```c filename=a_narrow_unsigned_index_below_a_constant_bound_indexes_a_global_array.c
int32 values[4];

int32 read_byte(uint8 x) {
    int32 r;
    r = 0;
    if (x < 4) {
        r = values[x];
    }
    return r;
}

void write_byte(uint8 x) {
    if (0 <= x && x < 4) {
        values[x] = 7;
    }
}

int32 read_half(uint16 x) {
    int32 r;
    r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}

void write_half(uint16 x) {
    if (x < 4) {
        values[x] = 7;
    }
}
```

```click
verifying "a_narrow_unsigned_index_below_a_constant_bound_indexes_a_global_array.c";

int32 read_byte(uint8 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_byte(uint8 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}

int32 read_half(uint16 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_half(uint16 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
pass
```
