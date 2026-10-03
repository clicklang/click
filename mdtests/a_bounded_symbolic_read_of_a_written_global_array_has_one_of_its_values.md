# A bounded symbolic read of a written global array has one of its values

The global counterpart of
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_has_one_of_its_values.md`:
the function writes every element of `values` before the read.

```c filename=a_bounded_symbolic_read_of_a_written_global_array_has_one_of_its_values.c
int32 values[4];

int32 g(int32 x) {
    int32 r = 0;
    values[0] = 1;
    values[1] = 2;
    values[2] = 3;
    values[3] = 4;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_written_global_array_has_one_of_its_values.c";

int32 g(int32 x) {
    owns values[0..4];
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
