# A `void *` is not dereferenced in a spec

C forbids `*v` for a `void *` `v` (C11 6.5.3.2p4 gives it no object type
to read). A spec likewise does not invent one: it casts to a typed pointer
or states the type with `load<T>`. Before this was refused, `*(p as (void
*))` silently read an `int32`, so it proved a read of an `int32` cell and
read only four bytes of an `int64` cell.

```c filename=void_pointer_spec_dereference_is_refused.c
int32 first(int32 *p) {
    return p[0];
}
```

```click
verifying "void_pointer_spec_dereference_is_refused.c";

int32 first(int32 *p) {
    views p[0..1];
    ensures result == *(p as (void *));
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
