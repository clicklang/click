# A symbolic read one past an initialized local array is refused

The bound control for
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md`.
Under `0 <= x < 5`, `x == 4` reads the four bytes just past `values`. No
initializer and no store wrote them, so the read is refused: the cells and
the initialization record cover `values[0..4]` and not the element past it.

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
fail: undefined behavior: read of uninitialized storage
```
