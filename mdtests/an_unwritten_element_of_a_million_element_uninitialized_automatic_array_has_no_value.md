# an unwritten element of a million-element uninitialized automatic array has no value

Only an automatic array declared with an initializer is zero-filled. One
declared without an initializer is uninitialized, however long it is, so
reading an element no statement wrote is undefined behavior rather than a
zero.

```c filename=an_unwritten_element_of_a_million_element_uninitialized_automatic_array_has_no_value.c
int32 read(void) {
    int32 buf[1000000];
    buf[0] = 1;
    return buf[5];
}
```

```click
verifying "an_unwritten_element_of_a_million_element_uninitialized_automatic_array_has_no_value.c";

int32 read() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
