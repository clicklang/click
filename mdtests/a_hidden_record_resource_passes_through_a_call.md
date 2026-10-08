# A resource with a hidden record passes through a call

`pair` declares no field and names a child that has one, so it keeps the
child's field in a record the author does not write. It is still held by
name, and a call that takes it binds the callee's instance to the caller's
with the usual map: `step(get(p), { x: x })`. The callee's postcondition
then holds of the caller's result.

```c filename=a_hidden_record_resource_passes_through_a_call.c
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

verifying "a_hidden_record_resource_passes_through_a_call.c";

int32 get(struct pair* p) {
    owns x: pair(p);
    ensures result >= 0;
} by {
    let { first: c } = unfold(x);
    execute();
    have result == c.v;
    let x = fold(pair(p), { first: c });
    simp();
}

int32 twice(struct pair* p) {
    owns x: pair(p);
    ensures result >= 0;
} by {
    let r = step(get(p), { x: x });
    execute();
    simp();
}
```

```expect
pass
```
