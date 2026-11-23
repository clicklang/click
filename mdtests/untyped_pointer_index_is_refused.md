# Indexing a `Pointer` is refused

A `Pointer` has no pointee type, so `q[i]` has no element to read. A read
through one states its type, `load<T>(q)`, or casts it first.

```c filename=untyped_pointer_index.c
int32 first(int32 *p) {
    return p[0];
}
```

```click
verifying "untyped_pointer_index.c";

int32 first(int32 *p) {
    views p[0..1];
    ensures result == (p as Pointer)[0];
}
```

```expect
fail: a `Pointer` has no pointee type; cast it to a typed pointer or use `load<T>`
```
