# A `long long` view of a struct is refused

A struct object admits a scalar access only of a class one of its members
has (C11 6.5p7). `struct a` contains only an `int`, so a `long long` read of
it through a `void *` round trip is refused.

```c filename=structs.c
struct a { int x; };

long long member_rank(struct a *pa) {
    void *v = pa;
    long long *q = v;
    return *q;
}
```

```click
verifying "structs.c";

long long member_rank(struct a *pa) {
    views pa->x;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct a` accessed through an lvalue of type `long long`
```
