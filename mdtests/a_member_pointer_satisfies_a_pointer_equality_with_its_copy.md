# A member pointer satisfies a pointer equality with its own copy

The positive control for
`a_one_past_member_pointer_does_not_satisfy_a_pointer_equality.md`. The
caller passes the same member pointer twice, once through a pointer field,
so the two arguments are one pointer value and `update` may read through
`h->value` with the permission `p` carries. A pointer formed by arithmetic
inside its own member, `&pair->first + 0`, is the same value too.

```c filename=fields.c
struct Pair { int first; int second; };
struct holder { const int *value; };
int update(struct holder *h, int *p) {
    *p = 7;
    return h->value[0];
}
int caller(struct Pair *pair, struct holder *h) {
    h->value = &pair->second;
    return update(h, &pair->second);
}
int offset(struct Pair *pair, struct holder *h) {
    h->value = &pair->first + 0;
    return update(h, &pair->first);
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
int32 offset(struct Pair *pair, struct holder *h) {
    owns pair->first;
    owns pair->second;
    owns h->value;
    ensures result == 7 by auto();
}
```

```expect
pass
```
