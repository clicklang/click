# A `long long` view of a local struct array is refused

A local array of structs records its struct on its block, so it is told
apart from a byte array: its elements admit the classes of the struct's
members, and `struct pair` has no `long long`.

```c filename=pairs.c
struct pair { int a; long b; };

long long view(void) {
    struct pair items[2];
    items[0].a = 1;
    items[0].b = 5;
    void *v = items;
    long long *q = v;
    return q[1];
}
```

```click
verifying "pairs.c";

long long view() {
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct pair` accessed through an lvalue of type `long long`
```
