# A declared struct read through another struct is refused

A local struct's declaration is authoritative: its block records its type,
so a member access through any other struct type is refused, whatever
pointer reaches it.

```c filename=structs.c
struct a { int x; };
struct b { int y; };

int local_probe(void) {
    struct a s;
    s.x = 1;
    void *v = &s;
    struct b *pb = v;
    return pb->y;
}
```

```click
verifying "structs.c";

int32 local_probe() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `struct a` accessed through an lvalue of type `struct b`
```
