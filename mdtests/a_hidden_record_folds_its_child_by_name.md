# A hidden record folds its child by name

`pair` declares no field, so its fold's one brace is the child map. When the
child it owns is bound to the slot's own name, `first`, the map is left out
and `fold(pair(p));` takes `first` by name; the hidden field `first.v` is
read from that child as it is from a written map.

```c filename=a_hidden_record_folds_its_child_by_name.c
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

verifying "a_hidden_record_folds_its_child_by_name.c";

int32 get(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
} by {
    let { first: first } = unfold(pair(p));
    execute();
    have result == first.v;
    fold(pair(p));
    simp();
}
```

```expect
pass
```
