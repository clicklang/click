# A member pointer parameter fills a clause of its member

The control for `a_member_pointer_parameter_keeps_its_subobject_beside_a_sibling_view.md`:
the callee's `q` adopts `&p->first`'s extent from its precondition, spelled
through another parameter, and its own one-element clause lies inside it.

```c filename=parameter_member_control.c
struct Pair { int32 first; int32 second; };
int32 second_of(struct Pair* p, int32* q) { return q[0]; }
int32 probe(struct Pair* p) { return second_of(p, &p->first); }
```

```click
verifying "parameter_member_control.c";
int32 second_of(struct Pair* p, int32* q) {
    views p->second;
    views q[0..1];
    requires q == &p->first;
    ensures result == q[0];
} by { execute(); simp(); }

int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->first;
} by { execute(); simp(); }
```

```expect
pass
```
