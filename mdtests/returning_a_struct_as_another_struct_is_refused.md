# Returning a struct as another struct is refused

A function's callers access what a returned pointer designates through
the declared return type. Returning a `struct a`, through a `void *`, as a
`struct b *` is refused, while returning it as a `struct a *` verifies.

```c filename=returns.c
struct a { int x; };
struct b { int y; };

struct b *as_b(struct a *pa) {
    void *v = pa;
    return v;
}
```

```click
verifying "returns.c";

struct b *as_b(struct a *pa) {
    ensures true;
} by {
    execute();
}
```

```expect
fail: `as_b` returns a pointer to an object of type `struct a` as a pointer to `struct b`
```
