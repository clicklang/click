# A struct read through a pointer to another struct is refused

Two struct types with the same layout are still distinct types (C11 6.5p7),
and GCC at `-O2` assumes a `struct b` lvalue never reads a `struct a`. A
member access names the struct it goes through, so after a `void *` round
trip `pb->y` is refused although `y` and `x` are both the `int` at offset 0.

```c filename=structs.c
struct a { int x; };
struct b { int y; };

int probe(struct a *pa) {
    void *v = pa;
    struct b *pb = v;
    return pb->y;
}
```

```click
verifying "structs.c";

int32 probe(struct a *pa) {
    views pa->x;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct a` accessed through an lvalue of type `struct b`
```
