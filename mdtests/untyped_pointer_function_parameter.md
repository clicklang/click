# A pure function takes a `Pointer` parameter

A `Pointer` parameter takes any object pointer argument: the argument keeps
its value, as Click's untyped pointer states no pointee type to convert to.
Equality between two `Pointer` values compares the whole value.

```c filename=untyped_pointer_parameter.c
struct node {
    int32 *next;
    int32 v;
};

int32 *next_of(struct node *s) {
    return s->next;
}
```

```click
verifying "untyped_pointer_parameter.c";

function same(q: Pointer, r: Pointer) -> Bool { q == r }

int32 *next_of(struct node *s) {
    views s->next;
    ensures same(result, s->next);
    ensures same(load<Pointer>(&s->next), result);
}
```

```expect
pass
```
