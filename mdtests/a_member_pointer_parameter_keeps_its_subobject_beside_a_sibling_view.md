# A member pointer parameter keeps its subobject beside a sibling view

`second_of` bounds `q` by one element, which the caller's `&p->first`
satisfies, and also views `p->second` through `p`. Reading `q[1]` would use
that view at `second`'s address, but `q` designates only `first`.

```c filename=parameter_member.c
struct Pair { int32 first; int32 second; };
int32 second_of(struct Pair* p, int32* q) { return q[1]; }
int32 probe(struct Pair* p) { return second_of(p, &p->first); }
```

```click
verifying "parameter_member.c";
int32 second_of(struct Pair* p, int32* q) {
    views p->first;
    views p->second;
    views q[0..1];
    ensures result == p->second;
} by { execute(); simp(); }

int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views q[1]`
```
