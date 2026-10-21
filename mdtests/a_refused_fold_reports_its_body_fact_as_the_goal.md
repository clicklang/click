# A refused fold reports its body fact as the goal

A fold whose proposed field makes an arm's body fact false is refused. The
refusal's summary quotes the declared fact (`*p == value`), after its ordinal,
and the instantiated fact it could not establish is the report's `goal:`, as
for every other proof error.

```c filename=fold_goal.c
void probe(int32 *p) {
    return;
}
```

```click
verifying "fold_goal.c";
spec enum Model { Node(int32) }
resource cell(p: int32*) {
    field model: Model;
    match model {
        Model::Node(value) => {
            owns *p;
            fact value >= 0;
            fact *p == value;
        },
    }
}
void probe(int32* p) {
    owns *p;
    requires *p == 3;
    ensures true;
} by {
    let wrong = fold(cell(p), { model: Model::Node(4) });
    execute();
}
```

```expect
fail: goal: old(p[0]) == 4
```
