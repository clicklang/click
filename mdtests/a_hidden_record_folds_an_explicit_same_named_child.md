# A hidden record folds an explicit same-named child

A fieldless parent still supplies its child in the fold input map. The
explicit binding supplies the hidden field `first.v`.

```c filename=a_hidden_record_folds_an_explicit_same_named_child.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

int32 get(struct pair* p) {
    return p->n;
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

verifying "a_hidden_record_folds_an_explicit_same_named_child.c";

int32 get(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
} by {
    let { first: first } = unfold(pair(p));
    step_until(function.exit);
    have result == first.v;
    fold(pair(p), { first: first });
    close();
}
```

```expect
pass
```
