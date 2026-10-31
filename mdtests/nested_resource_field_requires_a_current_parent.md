# A current child-field path requires its parent to be held

`pair(p).first.v` selects the hidden field in the exact parent instance.
The current path works while folded; `old(...)` retains its entry value
after unfolding. Naming the field does not unfold its child.

```c filename=nested_resource_field_requires_a_current_parent.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

int32 get(struct pair* p) {
    return p->n;
}

int32 twice(struct pair* p) {
    return get(p) + 0;
}
```

```click
resource counted(c: struct cell*) {
    field v: int32;
    owns c->value;
    fact c->value == v;
}

resource pair(p: struct pair*) {
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact p->n == first.v;
    fact first.v >= 0;
}

verifying "nested_resource_field_requires_a_current_parent.c";

int32 get(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
} by {
    have pair(p).first.v == old(pair(p).first.v);
    let { first: c } = unfold(pair(p));
    have c.v == pair(p).first.v;
    step_until(function.exit);
    have result == c.v;
    fold(pair(p), { first: c });
    have pair(p).first.v == result;
    solve();
}

int32 twice(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
}
```

```expect
fail: reads a field of `pair(p)`, which is not held here
```
