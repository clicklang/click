# A bounded symbolic read of an initialized local array is initialized

`values[x]` under `0 <= x && x < 4` reads one of four elements every one of
which was written, by the declaration's initializer or by statements, so the
read is an initialized element. It used to be refused as a read of
uninitialized storage.

The load splits once per stored cell it cannot place: `x == 0` reads the
first, and the case that `x` is none of them reads the memory without those
cells. That memory names the value only; dropping a cell there also dropped
its initialization mark, so the last case found no written bytes under the
index and reported undefined behavior. Whether the bytes were written is a
question about the memory the program holds, which still holds every cell, so
each case now asks it of that memory: its initialization record together
with its cached constant-offset cells, the bytes a store wrote and nothing
forgot.

The five functions are the fully initialized array, a partial initializer
whose rest is zero, `{0}`, an array every element of which a statement
assigned, and the same read through an unsigned index whose `x < 4u` bounds
it. The value read is initialized but not named: `result == result` holds on
every path.
`mdtests/a_symbolic_read_that_may_hit_an_unassigned_local_element_is_undefined.md`
is the negative.

```c filename=a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.c
int32 full(int32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 1;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}

int32 partial(int32 x) {
    int32 values[4] = {1};
    int32 r;
    r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}

int32 zero(int32 x) {
    int32 values[4] = {0};
    int32 r;
    r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}

int32 assigned(int32 x) {
    int32 values[4];
    int32 r;
    values[0] = 1;
    values[1] = 2;
    values[2] = 3;
    values[3] = 4;
    r = 1;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}

int32 unsigned_index(uint32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 1;
    if (x < 4u) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.c";

int32 full(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int32 partial(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int32 zero(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int32 assigned(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int32 unsigned_index(uint32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
