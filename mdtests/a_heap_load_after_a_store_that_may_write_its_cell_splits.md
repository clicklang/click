# A heap load after a store that may write its cell splits after the null check

`malloc` may fail, so `execute()` first splits on `buf == 0`. On the
allocated path, `buf[u] = 7` may or may not write `buf[0]`, so the load
`r = buf[0]` has two cases, and the `free` and `return` after it run once in
each. In the case `u == 0` the load reads the stored `7`; otherwise it reads
the `3` stored first. The stepped proof writes both splits as proof `if`s.

Two things refused this before. Planning certified each case's transition
against the ambient facts alone, so the case's own condition `u == 0` was
asked to follow from facts that only bound `u`; it is the case's assumption,
which the split supplies. And the store forgot that `buf[0]` was initialized
when it forgot the cell's value, so the case `u != 0` read "uninitialized
storage" although `buf[0] = 3` wrote it: a store initializes the bytes it may
write and leaves the others as they were.

The case `u != 0` then read an unknown value instead of the `3`. The store
`buf[u] = 7` dropped the cached `buf[0]`, and the name a load gets is decided
without any path's facts, so it stopped at that store. The same program over
a file-scope array read the `3` only because its reduced memory happened to
equal the snapshot before the store; a heap store also records the bytes it
initialized, which kept the two apart. A C read whose cell no cached value
answers now reads it from the recorded history under its own path's facts:
`u != 0` places the store off `buf[0]`, and the cell's value before the store
is the `3`.

```c filename=a_heap_load_after_a_store_that_may_write_its_cell_splits.c
int32 read_back(int32 u) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = buf[0];
    free(buf);
    return r;
}

int32 read_back_stepped(int32 u) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
verifying "a_heap_load_after_a_store_that_may_write_its_cell_splits.c";

int32 read_back(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
} by {
    execute();
    simp();
}

int32 read_back_stepped(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
} by {
    step();
    step();
    step();
    if buf == 0 {
        execute();
        simp();
    } else {
        step();
        step();
        step();
        step();
        if u == 0 {
            step();
            step();
            step();
            simp();
        } else {
            step();
            step();
            step();
            simp();
        }
    }
}
```

```expect
pass
```
