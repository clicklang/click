# A `branch ensuring` exports a resource whose model differs between its arms

The two arms of the C `if` store different values and refold the cell with
different models. `owns c: cell(node);` in the interface names the instance
the joined proof holds, with a fresh model, and the `fact` states what both
arms establish about it.

```c filename=branch_ensuring_named_resource.c
struct cell { int32 value; };

void set_sign(struct cell *node, int32 x) {
    if (x > 0) {
        node->value = 1;
    } else {
        node->value = 2;
    }
}
```

```click
verifying "branch_ensuring_named_resource.c";

resource cell(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

void set_sign(struct cell* node, int32 x) {
    requires node != 0;
    owns c: cell(node);
    ensures c.model >= 1;
} by {
    unfold(c);
    branch ensuring {
        owns c: cell(node);
        fact c.model >= 1;
    } then {
        step();
        let c = fold(cell(node), { model: 1 });
    } else {
        step();
        let c = fold(cell(node), { model: 2 });
    }
    step();
    simp();
}
```

```expect
pass
```
