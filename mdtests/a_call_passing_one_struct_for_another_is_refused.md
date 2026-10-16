# A call passing one struct for another is refused

A struct pointer parameter promises its struct. Passing a `struct a`, through
a `void *`, to a `struct b *` parameter is refused at the call, although the
two structs have the same layout.

```c filename=calls.c
struct a { int x; };
struct b { int y; };
int read_b(struct b *p) { return p->y; }

int caller_struct(struct a *pa) {
    void *v = pa;
    return read_b(v);
}
```

```click
verifying "calls.c";

int32 read_b(struct b *p) {
    views p->y;
    ensures true;
} by {
    execute();
}

int32 caller_struct(struct a *pa) {
    views pa->x;
    ensures true;
} by {
    execute();
}
```

```expect
fail: call to `read_b` passes an object of type `struct a` to parameter `p`, which points to `struct b`
```
