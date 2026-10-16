# A refused fold shows the hidden record it proposed

`clear` stores `-1` into `p->n`, so refolding `pair(p)` from the child `c`
fails at the body fact `p->n == first.v`. That fact reads `pair`'s hidden
record, so the refusal shows the record the fold proposed beside the failed
fact: `first.v` is the value the fact calls `<unnamed A>`.

```c filename=a_refused_fold_shows_the_hidden_record_it_proposed.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

void clear(struct pair* p) {
    p->n = -1;
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

verifying "a_refused_fold_shows_the_hidden_record_it_proposed.c";

void clear(struct pair* p) {
    owns x: pair(p);
} by {
    let { first: c } = unfold(x);
    execute();
    let x = fold(pair(p), { first: c });
    simp();
}
```

```expect
fail: proposed fold: pair(p) record { first.v: <unnamed A> }
```
