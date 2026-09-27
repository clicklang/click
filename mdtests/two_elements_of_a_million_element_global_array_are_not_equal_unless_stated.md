# two elements of a million-element global array are not equal unless stated

The entry values of a global array the function knows nothing about are
named lazily, one load identity per element read, and naming them lazily must
not make two elements share a value. `same` returns whether `buf[0]` and
`buf[1]` are equal, so claiming it returns `1` is refused: the path where the
two differ returns `0`.

The companion `same_when_stated` makes the same claim under a precondition
that the two are equal, and verifies.

```c filename=two_elements_of_a_million_element_global_array_are_not_equal_unless_stated.c
int32 buf[1000000];

int32 same() {
    return buf[0] == buf[1];
}

int32 same_when_stated() {
    return buf[0] == buf[1];
}
```

```click
verifying "two_elements_of_a_million_element_global_array_are_not_equal_unless_stated.c";

int32 same_when_stated() {
    requires buf[0] == buf[1];
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 same() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 1; left side evaluated to 0, right side evaluated to 1
```
