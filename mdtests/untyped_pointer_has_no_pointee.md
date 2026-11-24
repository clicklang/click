# A `Pointer` is not dereferenced

A `Pointer` has no pointee type, so `*q` has no type to read at. A read
through one states its type, `load<T>(q)`, or casts it to a typed pointer
first.

```c filename=untyped_pointer_has_no_pointee.c
int32 first(int32 *p) {
    return p[0];
}
```

```click
verifying "untyped_pointer_has_no_pointee.c";

int32 first(int32 *p) {
    views p[0..1];
    ensures result == *(p as Pointer);
}
```

```expect
fail: a `Pointer` has no pointee type; cast it to a typed pointer or use `load<T>`
```
