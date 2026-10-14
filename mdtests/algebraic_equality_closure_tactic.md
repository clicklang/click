# Checked tactic model equalities participate in shared equality closure

The postcondition and the match-arm equality are checked facts. Neither is
republished through a redundant `have` before proving the old model's constructor.

```c filename=model_alias.c
void user(int32 *p) { }
```

```click
verifying "model_alias.c";
spec enum Model { Empty, Node(int32) }
resource marker(p: int32*) {
    field model: Model;
    owns p[0..1];
}
tactic identity(p: int32*) {
    consumes x: marker(p);
    produces y: marker(p);
    ensures y.model == old(x.model);
} by {
    match x.model {
        Model::Empty => {
            unfold(x);
            let y = fold(marker(p), { model: Model::Empty });
            have y.model == old(x.model);
        },
        Model::Node(v) => {
            unfold(x);
            let y = fold(marker(p), { model: Model::Node(v) });
            have y.model == old(x.model);
        },
    }
}
void user(int32* p) {
    consumes x: marker(p);
    produces y: marker(p);
    ensures y.model == old(x.model);
} by {
    let { y: y } = identity(p, { x: x });
    match y.model {
        Model::Empty => { have old(x.model) == Model::Empty by { simp(); } execute(); simp(); },
        Model::Node(v) => { have old(x.model) == Model::Node(v) by { simp(); } execute(); simp(); },
    }
}
```

```expect
pass
```
