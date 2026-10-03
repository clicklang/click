# a tactic's recursion is ranked by an expression measure

`decreases x;` ranks a recursive C function by checking the argument of each
recursive call in its body. A tactic runs no code: its recursion happens in its
proof, where no body call exists to check, so a structural measure there would
rank nothing and is refused. An expression measure is owed at each
application instead
([`user_tactic_recursion_converts_a_list.md`](user_tactic_recursion_converts_a_list.md)).

```c filename=user_tactic_recursion_refuses_a_structural_measure.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_recursion_refuses_a_structural_measure.c";

spec enum Links { Nil, Cons(Links) }

resource list_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns &p->next;
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
            owns &p->next;
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
            have y.model == old(x.model) by { simp(); }
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            let { y: r2 } = convert(p->next) { x: r };
            have r2.model == rest_model by { simp(); }
            let y = fold(list2_at(p), { model: Links::Cons(rest_model) }, { rest: r2 });
            have y.model == old(x.model) by { simp(); }
        },
    }
}

void user(struct node* p) {
    consumes a: list_at(p);
    produces b: list2_at(p);
} by {
    let { y: b } = convert(p) { x: a };
    step();
    step();
    simp();
}
```

```expect
fail: `convert` recurses through a tactic application, which only an expression `decreases` measure can rank
```
