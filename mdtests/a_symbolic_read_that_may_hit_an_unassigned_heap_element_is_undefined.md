# A symbolic read that may hit an unassigned heap element is undefined

The negative for
`mdtests/a_bounded_symbolic_read_of_written_heap_cells_is_initialized.md`.
Nothing stores `p[2]` of the fresh allocation, so under `0 <= x < 4` the read
`p[x]` may read a byte no store wrote: a read of uninitialized storage.

```c filename=a_symbolic_read_that_may_hit_an_unassigned_heap_element_is_undefined.c
int32 heap_some(int32 x) {
    int32* p;
    int32 r;
    p = malloc(16);
    if (p == 0) {
        return 0;
    }
    p[0] = 1;
    p[1] = 2;
    p[3] = 4;
    r = p[x];
    free(p);
    return r;
}
```

```click
verifying "a_symbolic_read_that_may_hit_an_unassigned_heap_element_is_undefined.c";

int32 heap_some(int32 x) {
    requires 0 <= x;
    requires x < 4;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
