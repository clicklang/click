# structural recursion completion follows the ordinary proof path

The call in the concretely false loop creates no descent obligation. The
live recursive call passes an unfolded child of the entry model. Completion
must retain that evidence rather than analyze both calls again from C.

```c filename=c_decreases_binder_avoids_recursive_loop.c
struct node { struct node *next; };

int32 walk_list(struct node* p) {
    int32 result;
    while (0) { walk_list(p); }
    if (p != 0) {
        result = walk_list(p->next);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_binder_avoids_recursive_loop.c";

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

int32 walk_list(struct node* p) {
    owns x: list_at(p);
    decreases x;
    ensures result == 0;
    ensures x.model == old(x.model);
} by {
    step();
    step();
    match x.model {
        Links::Nil => {
            unfold(x);
            step();
            let x = fold(list_at(p), { model: Links::Nil });
            step();
            step();
            solve();
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            step();
            step();
            let x = fold(list_at(p), { model: Links::Cons(rest_model) }, { rest: r });
            step();
            step();
            solve();
        },
    }
}
```

```expect
pass
```
