# A global struct read through another struct is refused

A global struct records its struct on its block, so a member access through
a struct of another type, though of the same layout, is refused.

```c filename=globals.c
struct a { int x; };
struct b { int y; };
struct a shared;

int read_shared(void) {
    void *v = &shared;
    struct b *pb = v;
    return pb->y;
}
```

```click
verifying "globals.c";

int32 read_shared() {
    owns shared.x;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct a` accessed through an lvalue of type `struct b`
```
