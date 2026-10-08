# A parent with fields states facts about a child's field

`pair` declares the field `first_v` and names the child `first`, whose field
`v` the equation `fact first.v == first_v;` keeps there. After that equation
`first.v` in the body reads `first_v`, so the second fact, `p->n ==
first.v`, is an ordinary fact about the parent's field and not a second
equation for the child's.

`get` returns `p->n`, and the contract claims it is the field.

The equation comes first. `a_fact_about_a_childs_field_before_its_equation_is_refused.md`
is the other order.

```c filename=a_parent_with_fields_states_facts_about_a_childs_field.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

int32 get(struct pair* p) {
    return p->n;
}

void set(struct pair* p) {
    p->n = p->a->value;
}
```

```click
resource counted(c: struct cell*) {
    field v: int32;
    owns c->value;
    fact c->value == v;
}

resource pair(p: struct pair*) {
    field first_v: int32;
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact first.v == first_v;
    fact p->n == first.v;
}

verifying "a_parent_with_fields_states_facts_about_a_childs_field.c";

int32 get(struct pair* p) {
    owns x: pair(p);
    ensures result == x.first_v;
} by {
    let { first: c, first_v: v } = unfold(x);
    execute();
    let x = fold(pair(p), { first_v: v }, { first: c });
    simp();
}
```

```expect
pass
```
