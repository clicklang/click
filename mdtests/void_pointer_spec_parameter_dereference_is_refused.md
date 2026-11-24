# A `void *` parameter is not dereferenced in a spec

```c filename=void_pointer_spec_parameter_dereference_is_refused.c
uint8 first(void *q) {
    return *(uint8 *)q;
}
```

```click
verifying "void_pointer_spec_parameter_dereference_is_refused.c";

uint8 first(void *q) {
    views (q as (uint8 *))[0..1];
    ensures result == *q;
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
