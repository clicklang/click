# A `void *` steps back by one byte in a spec

`q - k` on a `void *` steps back `k` bytes, as the C body's `q - k` does.

```c filename=void_pointer_spec_subtraction_steps_one_byte.c
void *prev(void *q) {
    return q - 1;
}
```

```click
verifying "void_pointer_spec_subtraction_steps_one_byte.c";

void *prev(void *q) {
    ensures result == q - 1;
}
```

```expect
pass
```
