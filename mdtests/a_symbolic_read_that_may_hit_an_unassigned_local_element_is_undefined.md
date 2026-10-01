# A symbolic read that may hit an unassigned local element is undefined

The negative for
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md`.
`values` has no initializer and nothing assigns `values[2]`, so under
`0 <= x < 4` the read `values[x]` may read it. The cells the stores left
cover elements 0, 1 and 3 only, and the read is still a read of
uninitialized storage.

```c filename=a_symbolic_read_that_may_hit_an_unassigned_local_element_is_undefined.c
int32 some_assigned(int32 x) {
    int32 values[4];
    int32 r;
    values[0] = 1;
    values[1] = 2;
    values[3] = 4;
    r = 1;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_symbolic_read_that_may_hit_an_unassigned_local_element_is_undefined.c";

int32 some_assigned(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
