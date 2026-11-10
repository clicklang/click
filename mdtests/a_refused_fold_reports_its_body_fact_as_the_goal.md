# A refused fold reports its body fact as the goal

A fold whose proposed field makes an arm's body fact false is refused. The
refusal names the instantiated obligation `*p == (4 as int32)`, using the caller's source
names rather than the resource definition's field placeholder.

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
}
```

```expect
fail: unproved obligation: `*p == (4 as int32)`
```
