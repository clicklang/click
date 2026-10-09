# An unsigned index that wraps below zero is refused

`x < 4u` bounds `x`, but not `x - 1u`: at `x == 0` the difference wraps to
`4294967295`, far past `values`. No fact bounds the wrapped word, so the
index keeps its exact zero-extended value. Computing the element address
is refused because the pointer arithmetic leaves the array.

```c filename=an_unsigned_index_that_wraps_below_zero_is_refused.c
int32 read_previous(uint32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 0;
    if (x < 4u) {
        r = values[x - 1u];
    }
    return r;
}
```

```click
verifying "an_unsigned_index_that_wraps_below_zero_is_refused.c";

int32 read_previous(uint32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
