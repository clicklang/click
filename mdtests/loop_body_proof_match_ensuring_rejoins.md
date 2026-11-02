# A loop-body proof `match` rejoins through its interface

Each arm opens the cell and refolds it with its own constructor, so the arms
end the same way but hold cells with different models. `ensuring` names the
cell the rejoined body holds. The arms rejoin inside the body, as the arms of
a `branch` do, and the rest of the iteration (the C step and the invariants)
is checked once, on the one path that leaves the `match`, not once per arm.

```c filename=loop_body_proof_match_ensuring_rejoins.c
struct cell { int32 value; };

void spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "loop_body_proof_match_ensuring_rejoins.c";

spec enum Sign { Neg(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value >= 0;
        },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;

        initialize by solve();
        preserve by {
            match c.model ensuring {
                owns c: cell(node);
            } {
                Sign::Neg(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                }
                Sign::Pos(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                }
            }
            step();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
