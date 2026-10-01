# A bounded symbolic field read of an initialized struct array is initialized

The struct-array counterpart of
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md`.
`items[x].y` under `0 <= x < 2` reads a field the initializer wrote. The load
splits on the initializer's cells it cannot place, and the case past them
used to find no written bytes under the index; the cells of the memory the
program holds cover the read, so it is an initialized field.

```c filename=a_bounded_symbolic_field_read_of_an_initialized_struct_array_is_initialized.c
struct point {
    int32 x;
    int32 y;
};

int32 field(int32 x) {
    struct point items[2] = {{1, 2}, {3, 4}};
    return items[x].y;
}
```

```click
verifying "a_bounded_symbolic_field_read_of_an_initialized_struct_array_is_initialized.c";

int32 field(int32 x) {
    requires 0 <= x;
    requires x < 2;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
