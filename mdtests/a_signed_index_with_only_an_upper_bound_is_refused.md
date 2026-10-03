# A signed index with only an upper bound is refused

The signed control for
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_local_array.md`.
`x < 4` on an `int32` is a signed test and leaves `x` free below zero; only
the biased spelling of an unsigned test files a lower bound beside it.

```c filename=a_signed_index_with_only_an_upper_bound_is_refused.c
int32 write_local(int32 x) {
    int32 values[4] = {1, 2, 3, 4};
    if (x < 4) {
        values[x] = 7;
    }
    return values[0];
}
```

```click
verifying "a_signed_index_with_only_an_upper_bound_is_refused.c";

int32 write_local(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
