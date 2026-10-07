# An interface resource argument reads through a model pointer

Each arm holds `list(id->next)`, where `id` is the pointer the model binds
and the resource states `p == id`. No cell is filed under `id`: the cell is
under `n`. The join reads the argument in the joined state by following the
stated equality from `id` to `n`. `next` is the second field, so the read is
at an offset from the object.

```c filename=nl.c
struct node { int32 val; struct node *next; };

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
pass
```
