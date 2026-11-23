# `byte_offset` steps a `Pointer` by bytes

`byte_offset(q, n)` on a `Pointer` `q` is the `Pointer` `n` bytes on: a
`Pointer` has no pointee type to scale by, so the byte count is the whole
step. A typed load through the result reads the member there.

```c filename=untyped_pointer_byte_offset.c
struct pair {
    int32 a;
    int32 b;
};

int32 second(struct pair *p) {
    return p->b;
}
```

```click
verifying "untyped_pointer_byte_offset.c";

int32 second(struct pair *p) {
    views p->a;
    views p->b;
    ensures result == load<int32>(byte_offset(p as Pointer, 4));
}
```

```expect
pass
```
