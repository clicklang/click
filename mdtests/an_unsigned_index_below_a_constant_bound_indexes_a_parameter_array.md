# An unsigned index below a constant bound indexes a parameter array

`x < 4u` with `uint32 x` is lowered to the sign-biased signed comparison
`(-2147483648 ^ x) < -2147483644`. The access `values[x]` widens `x` to an
exact 64-bit element index, and neither the 64-bit pointer-formation guard
nor the `views` and `owns` coverage of `values[0..4]` could read the biased
spelling as a bound on `x`, so every read and write below was refused as
"pointer arithmetic left the pointed-to object" or a missing resource.

An unsigned bound below the sign bit holds exactly when the signed pair
`0 <= x` and `x < 4` does, and the fact set files that pair beside it; an
unsigned index whose sign bit the path has cleared then names the element
it names read as signed. The mirrored test `4u > x`, the inclusive
`x <= 3u`, and a `uint64` index bounded the same way take the same route.

```c filename=an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.c
int32 read_viewed(int32* values, uint32 x) {
    int32 r;
    r = 0;
    if (x < 4u) {
        r = values[x];
    }
    return r;
}

void write_owned(int32* values, uint32 x) {
    if (4u > x) {
        values[x] = 7;
    }
}

void write_owned_inclusive(int32* values, uint32 x) {
    if (x <= 3u) {
        values[x] = 7;
    }
}

int32 read_viewed_wide(int32* values, uint64 x) {
    int32 r;
    r = 0;
    if (x < 4u) {
        r = values[x];
    }
    return r;
}

void write_owned_wide(int32* values, uint64 x) {
    if (x < 4u) {
        values[x] = 7;
    }
}
```

```click
verifying "an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.c";

int32 read_viewed(int32* values, uint32 x) {
    views values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_owned(int32* values, uint32 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}

void write_owned_inclusive(int32* values, uint32 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}

int32 read_viewed_wide(int32* values, uint64 x) {
    views values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}

void write_owned_wide(int32* values, uint64 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
pass
```
