# A symbolic read of an unwritten local element is uninitialized

The in-bounds counterpart of
`mdtests/a_symbolic_read_one_past_an_initialized_local_array_is_refused.md`.
Under `0 <= x < 4` the read stays inside `values`, so the bound holds, but
only `values[0]` was written: the read is refused as a read of uninitialized
storage.

```c filename=a_symbolic_read_of_an_unwritten_local_element_is_uninitialized.c
int32 inside(int32 x) {
    int32 values[4];
    int32 r;
    values[0] = 1;
    r = 1;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_symbolic_read_of_an_unwritten_local_element_is_uninitialized.c";

int32 inside(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
