# A struct pointer loaded from a member designates its struct

A pointer read from a `struct node *` member designates a `struct node`, so
a member access through another struct type, after a `void *` round trip,
is refused, while one through `struct node` itself verifies.

```c filename=list.c
struct node { struct node *next; int v; };
struct other { int a; int b; };

int loaded(struct node *n) {
    struct node *m = n->next;
    void *v = m;
    struct other *o = v;
    return o->a;
}
```

```click
verifying "list.c";

int32 loaded(struct node *n) {
    views n->next;
    views n->next->v;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct node` accessed through an lvalue of type `struct other`
```
