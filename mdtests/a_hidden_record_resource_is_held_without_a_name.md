# A resource with a hidden record is held without a name

`pair` declares no field, so no contract could name one of its fields, and
it is held like any resource without fields: `owns pair(p);`. It is still
unfolded with its child bound, `let { first: c } = unfold(pair(p));`, and
folded from that child, `fold(pair(p), { first: c });`.

`twice` calls `get`, which holds the same resource. The caller owns exactly
one `pair`, so the call binds the callee's to it and no map is written.

```c filename=a_hidden_record_resource_is_held_without_a_name.c
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

verifying "a_hidden_record_resource_is_held_without_a_name.c";

int32 get(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
} by {
    let { first: c } = unfold(pair(p));
    execute();
    have result == c.v;
    fold(pair(p), { first: c });
    simp();
}

int32 twice(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
