# A bounded symbolic read of written heap cells is initialized

The heap counterpart of
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md`.
Every element of the fresh allocation is stored before `p[x]` reads one of
them. A heap store records the bytes it writes, but the load's case past the
stored cells reads a memory that dropped those cells and their marks, and it
was refused as a read of uninitialized storage. The memory the program holds
still records them, so the read is initialized.
`mdtests/a_symbolic_read_that_may_hit_an_unassigned_heap_element_is_undefined.md`
is the negative.

```c filename=a_bounded_symbolic_read_of_written_heap_cells_is_initialized.c
int32 heap_all(int32 x) {
    int32* p;
    int32 r;
    p = malloc(16);
    if (p == 0) {
        return 0;
    }
    p[0] = 1;
    p[1] = 2;
    p[2] = 3;
    p[3] = 4;
    r = p[x];
    free(p);
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_written_heap_cells_is_initialized.c";

int32 heap_all(int32 x) {
    requires 0 <= x;
    requires x < 4;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
