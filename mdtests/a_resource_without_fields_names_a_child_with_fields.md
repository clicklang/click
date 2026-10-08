# A resource without fields names a child that has them

`pair` declares no field and holds `first: counted(p->a)`, whose field `v`
two of its facts read. Nothing in `pair` says where the child's field is
kept: the resource holds it in a record the author does not write, so the
value survives a fold of `pair` as a declared field's would.

`get` unfolds `pair`, binding the child to `c`, reads `p->n`, which the
first fact ties to `c.v`, and folds `pair` back from the same child. The
fold takes only the child map; it supplies the hidden field from `c`.

`a_fold_over_a_hidden_record_still_checks_the_facts.md` is the fold whose
fact no longer holds.

```c filename=a_resource_without_fields_names_a_child_with_fields.c
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

verifying "a_resource_without_fields_names_a_child_with_fields.c";

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
```

```expect
pass
```
