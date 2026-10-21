# `sizeof` of a local array is its whole size

An array operand does not decay under `sizeof` (C11 6.3.2.1p3), so
`sizeof(values)` for `int32 values[3]` is `12`, not a pointer's `8`.

```c filename=c_sizeof_local_array.c
int32 size(int32 value) {
    int32 values[3];
    return sizeof(values);
}
```

```click
verifying "c_sizeof_local_array.c";

int32 size(int32 value) {
    ensures result == 12;
} by {
    execute();
    simp();
}
```

```expect
pass
```
