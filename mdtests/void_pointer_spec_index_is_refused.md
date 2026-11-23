# A `void *` is not indexed in a spec

A `void *` has no element type to step by, so `q[i]` in a spec is refused
rather than read as an `int32` four bytes on. Click once read this `q[1]` as
the `int32` at byte 4 of the `uint8` buffer.

```c filename=void_pointer_spec_index_is_refused.c
uint8 second(void *q) {
    return ((uint8 *)q)[1];
}
```

```click
verifying "void_pointer_spec_index_is_refused.c";

uint8 second(void *q) {
    views (q as (uint8 *))[0..2];
    ensures result == q[1];
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
