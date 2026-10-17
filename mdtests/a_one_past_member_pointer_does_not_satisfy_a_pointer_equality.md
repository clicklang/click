# A one-past member pointer does not satisfy a pointer equality

`&pair->first + 1` and `&pair->second` have one address but are different
pointers: the first is one past `first` and cannot be dereferenced
(C11 6.5.6p7-p8). A contract `==` between pointers is value equality,
subobject included (`design/pointer-subobject-extents.md`, D2), so the call
cannot establish `update`'s `h->value == p`. Otherwise `update` would read
through `h->value` with the permission `p` carries.

The C and contract are the original counterexample from
the scalar-subobject bug
(`bugs/pointer-arithmetic-crosses-scalar-subobject.md`, closed 2026-10-17),
unchanged.

```c filename=fields.c
struct Pair { int first; int second; };
struct holder { const int *value; };
int update(struct holder *h, int *p) {
    *p = 7;
    return h->value[0];
}
int caller(struct Pair *pair, struct holder *h) {
    h->value = &pair->first + 1;
    return update(h, &pair->second);
}
```

```click
verifying "fields.c";
int32 update(struct holder *h, int32 *p) {
    views h->value;
    owns p[0..1];
    requires h->value == p;
    ensures result == 7 by auto();
}
int32 caller(struct Pair *pair, struct holder *h) {
    owns pair->first;
    owns pair->second;
    owns h->value;
    ensures result == 7 by auto();
}
```

```expect
fail: missing prerequisite (precondition clause 3 of `update`)
```
