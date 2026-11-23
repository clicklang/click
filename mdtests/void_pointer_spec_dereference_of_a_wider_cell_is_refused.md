# A `void *` to a wider cell is not dereferenced in a spec

A `void *` dereference has no width to read at. Click once read it as an
`int32`, which reads four bytes of this `int64` cell; it is now refused.

```c filename=void_pointer_spec_dereference_of_a_wider_cell_is_refused.c
int64 first(int64 *p) {
    return p[0];
}
```

```click
verifying "void_pointer_spec_dereference_of_a_wider_cell_is_refused.c";

int64 first(int64 *p) {
    views p[0..1];
    ensures result == *(p as (void *));
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
