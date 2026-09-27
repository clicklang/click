# a stored allocation is freed through a global pointer element

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. A store of `q` into
one element makes that slot a hole holding `q`, so the read back for `free`
is the allocation the contract consumes.

```c filename=a_stored_allocation_is_freed_through_a_global_pointer_element.c
int32 *ptrs[100];

int32 store_then_free(int32 *q) {
    ptrs[7] = q;
    free(ptrs[7]);
    return 0;
}
```

```click
verifying "a_stored_allocation_is_freed_through_a_global_pointer_element.c";

int32 store_then_free(int32 *q) {
    consumes allocation(q, 4);
    consumes q[0..1];
    owns ptrs[0..100];
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
