# a stored-over element of a million-element automatic array is not its old value

An automatic array's initializer zero-fills it and stores the elements it
writes. A later store into an element, written or zero, replaces that element
alone, so a claim that it still holds its initial value is refused.

```c filename=a_stored_over_element_of_a_million_element_automatic_array_is_not_its_old_value.c
int32 read(void) {
    int32 buf[1000000] = {1, 2, 3};
    buf[1] = 9;
    buf[500] = 4;
    return buf[1] + buf[500];
}
```

```click
verifying "a_stored_over_element_of_a_million_element_automatic_array_is_not_its_old_value.c";

int32 read() {
    ensures result == 2;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 13, right side evaluated to 2
```
