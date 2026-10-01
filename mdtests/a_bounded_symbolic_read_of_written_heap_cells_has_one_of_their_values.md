# A bounded symbolic read of written heap cells has one of their values

The heap counterpart of
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_has_one_of_its_values.md`.

```c filename=a_bounded_symbolic_read_of_written_heap_cells_has_one_of_their_values.c
int32 h(int32 x) {
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
    r = 0;
    if (0 <= x && x < 4) {
        r = p[x];
    }
    free(p);
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_written_heap_cells_has_one_of_their_values.c";

int32 h(int32 x) {
    ensures result >= 0;
    ensures result <= 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
