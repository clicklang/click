# A `void *` steps by one byte in a spec

Click's C side steps a `void *` by one byte (the GNU extension), so a spec
means the same by `q + k` and `k + q`: `ensures result == q + 1` states the
C body's own step. Click once refused these, and before that stepped them
by four bytes.

```c filename=void_pointer_spec_addition_steps_one_byte.c
void *next(void *q) {
    return q + 1;
}

void *also_next(void *q) {
    return 1 + q;
}

void *as_bytes(void *q) {
    return (uint8 *)q + 1;
}
```

```click
verifying "void_pointer_spec_addition_steps_one_byte.c";

void *next(void *q) {
    ensures result == q + 1;
}

void *also_next(void *q) {
    ensures result == 1 + q;
}

void *as_bytes(void *q) {
    ensures result == q + 1;
}
```

```expect
pass
```
