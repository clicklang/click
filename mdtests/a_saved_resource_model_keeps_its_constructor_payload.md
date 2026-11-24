# A saved resource model keeps its constructor payload

The mark records the model of the refolded instance. After the instance is
unfolded, reading the model at that mark still returns its constructor and
the original pointer payload.

```c filename=saved_resource_model.c
struct node { int word; };
void stamp(struct node *p) { p->word = 7; }
```

```click
verifying "saved_resource_model.c";

spec enum Model { At(struct node*) }

resource cell(p: struct node*) {
    field model: Model;
    match model {
        Model::At(id) => {
            owns id->word;
            fact id == p;
        },
    }
}

void stamp(struct node* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
} by {
    match c.model {
        Model::At(first) => {
            unfold(c);
            let c = fold(cell(p), { model: Model::At(first) });
            mark packed;
            have (match c.model { Model::At(original) => original }) == first by known();
            match c.model {
                Model::At(second) => {
                    unfold(c);
                    have at(packed, c.model) == Model::At(first) by known();
                    have (match at(packed, c.model) { Model::At(original) => original }) == first by {
                        close() using {};
                    }
                    have second == first by known();
                    step();
                    let c = fold(cell(p), { model: old(c.model) });
                    step();
                    solve();
                },
            }
        },
    }
}
```

```expect
pass
```
