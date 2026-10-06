# A proof `if` rejoins arms that hold a resource with different models

One arm refolds the cell with its model spelled as the value just read; the
other leaves the cell alone. The arms end in different states, so they rejoin
through `ensuring`. `owns c: cell(node);` names the instance the rejoined
proof holds: each arm supplies the instance it has bound to `c`, and the join
gives `c` a fresh model. The `fact` is checked in each arm against that arm's
own model, and is all the proof knows about the fresh one afterwards.

```c filename=proof_if_ensuring_named_resource.c
struct cell { int32 value; };

int32 peek(struct cell *node, int32 x) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_if_ensuring_named_resource.c";

resource cell(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 peek(struct cell* node, int32 x) {
    requires node != 0;
    owns c: cell(node);
    ensures result == 0;
    ensures c.model == old(c.model);
} by {
    step();
    if x <= 0 ensuring {
        owns c: cell(node);
        fact c.model == old(c.model);
    } then {
        unfold(c);
        let c = fold(cell(node), { model: node->value });
    } else {
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
