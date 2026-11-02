# An interface fact in a loop body reads `old(...)` as function entry

The loop keeps the cell's model: `invariant c.model == old(c.model);`. Each arm
of the `match` refolds the cell with its own constructor, and the interface
states that the rejoined cell's model is still the entry model. `old(...)`
there means what it means in the invariant, the function's entry, so the
invariant closes on the one path that leaves the `match`.

```c filename=loop_body_proof_match_ensuring_old_fact.c
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
verifying "loop_body_proof_match_ensuring_old_fact.c";

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
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);

        initialize by solve();
        preserve by {
            match c.model ensuring {
                owns c: cell(node);
                fact c.model == old(c.model);
            } {
                Sign::Neg(value) => {
                    have Sign::Neg(value) == old(c.model) by {
                        rewrite(Sign::Neg(value) == c.model);
                        assumption();
                    }
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                    have c.model == old(c.model) by {
                        assumption();
                    }
                }
                Sign::Pos(value) => {
                    have Sign::Pos(value) == old(c.model) by {
                        rewrite(Sign::Pos(value) == c.model);
                        assumption();
                    }
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                    have c.model == old(c.model) by {
                        assumption();
                    }
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
