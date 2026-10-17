# A checked model pointer's type follows pointer equality

Matching the resource supplies a typed `identity`; opening it supplies
`p == identity`. The same model constructor must accept either spelling.

```c filename=typed_equal.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "typed_equal.c";
spec enum Ref { At(struct node*), }
resource token(p: struct node*) {
    field model: Ref;
    match model {
        Ref::At(identity) => { fact p == identity; },
    }
}
void keep(struct node* p) {
    owns held: token(p);
    ensures held.model == old(held.model);
} by {
    match held.model {
        Ref::At(identity) => {
            unfold(held);
            have p == identity by assumption();
            have Ref::At(p) == Ref::At(identity) by { simp(); }
            let held = fold(token(p), { model: Ref::At(identity) });
            execute(); simp();
        },
    }
}
```

```expect
pass
```
