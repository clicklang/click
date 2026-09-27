# a pointer read back from a global array after its free is invalid

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. The element written
with `q` still holds `q` after `q` is freed, and reading through it is an
invalid access.

```c filename=a_pointer_read_back_from_a_global_array_after_its_free_is_invalid.c
int32 *ptrs[100];

int32 read_after_free(int32 *q) {
    ptrs[7] = q;
    free(q);
    int32 *r = ptrs[7];
    return *r;
}
```

```click
verifying "a_pointer_read_back_from_a_global_array_after_its_free_is_invalid.c";

int32 read_after_free(int32 *q) {
    consumes allocation(q, 4);
    owns q[0..1];
    owns ptrs[0..100];
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: invalid memory access
```
