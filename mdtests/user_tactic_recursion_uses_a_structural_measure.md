# structural tactic recursion carries ordinary descent obligations

`decreases x;` ranks each recursive tactic application by the model of the
resource instance it passes. Unfolding `x` exposes a child whose model is
strictly contained in the entry model, just as for recursive C calls.

```c filename=user_tactic_recursion_uses_a_structural_measure.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_recursion_uses_a_structural_measure.c";

spec enum Links { Nil, Cons(Links) }

resource list_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns p->next;
            owns rest: list_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

resource list2_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns p->next;
            owns rest: list2_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

tactic convert(p: struct node*) {
    decreases x;
    consumes x: list_at(p);
    produces y: list2_at(p);
    ensures y.model == old(x.model);
} by {
    match x.model {
        Links::Nil => {
            unfold(x);
            let y = fold(list2_at(p), { model: Links::Nil });
            have y.model == old(x.model);
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            let { y: r2 } = convert(p->next, { x: r });
            have r2.model == rest_model;
            let y = fold(list2_at(p), { model: Links::Cons(rest_model), rest: r2 });
            have y.model == old(x.model);
        },
    }
}

void user(struct node* p) {
    consumes a: list_at(p);
    produces b: list2_at(p);
} by {
    let { y: b } = convert(p, { x: a });
    step();
    step();
    close();
}
```

```expect
pass
```
