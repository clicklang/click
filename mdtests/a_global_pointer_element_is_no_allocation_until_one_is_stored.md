# a global pointer element is no allocation until one is stored in it

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. An element of pointer
type holds a fresh symbolic pointer that no allocation resource names, so
freeing it is refused. `store_then_free` frees what it stored there, which
`a_stored_allocation_is_freed_through_a_global_pointer_element.md` verifies.

```c filename=a_global_pointer_element_is_no_allocation_until_one_is_stored.c
int32 *ptrs[100];

int32 free_unknown() {
    free(ptrs[7]);
    return 0;
}
```

```click
verifying "a_global_pointer_element_is_no_allocation_until_one_is_stored.c";

int32 free_unknown() {
    owns ptrs[0..100];
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: cannot free a pointer that is not a live heap allocation
```
