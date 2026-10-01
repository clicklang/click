# A symbolic read one past an initialized local array is refused for its bound

The bound control for
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md`.
Under `0 <= x < 5`, `x == 4` reads the four bytes just past `values`. The read
is refused for the index bound it could not show, not as a read of
uninitialized storage: the bounds obligation comes before the initialization
check, which only judges reads inside the object.
`mdtests/a_symbolic_read_of_an_unwritten_local_element_is_uninitialized.md` is
the in-bounds counterpart.

```c filename=a_symbolic_read_one_past_an_initialized_local_array_is_refused.c
int32 one_past(int32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r;
    r = 1;
    if (0 <= x && x < 5) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_symbolic_read_one_past_an_initialized_local_array_is_refused.c";

int32 one_past(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: the read of `values[x]` may read outside `values`: could not show `0 <= x && x < 4`
```
