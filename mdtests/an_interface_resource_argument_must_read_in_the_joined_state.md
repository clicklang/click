# An interface resource argument must read in the joined state

Each arm holds `list(id->next)`, where `id` is the pointer the model binds
and equals `n`. The joined state cannot read `id->next`, so the join is
refused by naming the clause and the two repairs. Writing `list(n->next)`
verifies.

```c filename=nl.c
struct node { struct node *next; int32 val; };

int32 peek(struct node *n, int32 x) {
    int32 a;
    struct node *m;
    a = 0;
    m = n->next;
    return a;
}
```

```click
verifying "nl.c";

spec enum Chain { Nil, Cons(struct node*, int32, Chain) }

resource list(p: struct node*) {
    field model: Chain;
    match model {
        Chain::Nil => { fact p == 0; },
        Chain::Cons(id, value, rest) => {
            fact p == id;
            owns p->val;
            owns &p->next;
            owns tail: list(p->next);
            fact p != 0;
            fact p->val == value;
            fact tail.model == rest;
        },
    }
}

int32 peek(struct node* n, int32 x) {
    requires n != 0;
    consumes l: list(n);
    ensures result == 0;
} by {
    step();
    step();
    match l.model {
        Chain::Nil => {
            unfold(l);
            contradiction(n == 0);
        },
        Chain::Cons(id, value, rest) => {
            let { tail: t } = unfold(l);
            match t.model ensuring {
                owns t: list(id->next);
            } {
                Chain::Nil => {
                    unfold(t);
                    step();
                    let t = fold(list(0), { model: Chain::Nil });
                },
                Chain::Cons(tid, w, more) => {
                    let { tail: u } = unfold(t);
                    step();
                    let t = fold(list(n->next), { model: Chain::Cons(tid, w, more) }, { tail: u });
                },
            }
            step();
            step();
            simp();
        },
    }
}
```

```expect
fail: the `ensuring` interface names `t: list(…->next)`, which each arm holds, but its arguments cannot be read in the state the arms join in
```
