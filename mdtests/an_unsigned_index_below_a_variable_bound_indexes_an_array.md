# An unsigned index below a variable bound indexes an array

The variable-bound counterpart of
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.md`.
The test `x < n` over `uint32` operands is the `uint32` order `x <u n`, and
`requires n <= 4u32` is `n <=u 4`. The difference graph composes the two in
its unsigned domain as it composes a signed chain, so `x <u 4` follows,
and with it the signed range `0 <= x`, `x < 4` the element and footprint
rules read. The same holds for a file-scope array, whose subscript check
`x >= 0 && x < 4` is a prerequisite the proof discharges.

```c filename=an_unsigned_index_below_a_variable_bound_indexes_an_array.c
int32 table[4];

void store_below(int32* values, uint32 x, uint32 n) {
    if (x < n) {
        values[x] = 0;
    }
}

int32 read_below(int32* values, uint32 x, uint32 n) {
    int32 r;
    r = 0;
    if (x < n) {
        r = values[x];
    }
    return r;
}

void store_global_below(uint32 x, uint32 n) {
    if (x < n) {
        table[x] = 1;
    }
}
```

```click
verifying "an_unsigned_index_below_a_variable_bound_indexes_an_array.c";

void store_below(int32* values, uint32 x, uint32 n) {
    requires n <= 4u32;
    owns values[0..4];
}

int32 read_below(int32* values, uint32 x, uint32 n) {
    requires n <= 4u32;
    owns values[0..4];
    ensures result == result;
}

void store_global_below(uint32 x, uint32 n) {
    requires n <= 4u32;
    owns table[0..4];
}
```

```expect
pass
```
