# A rejoined `match` inside a proof `if` keeps the `if` on its path

The loop body splits on a proof `if` whose arms each run to the end of the
iteration. Inside each arm a `match` rejoins through `ensuring`, and a second
`match` after it runs its arms to the end.

The path that leaves the rejoined `match` is still on the enclosing `if`'s
case: the join ends its own two cases, not the ones the proof took to reach
it. Dropping them left the four leaves of this body with no `if` to be
grouped under when their certificates were merged, and the body was refused
as having "incompatible next proof `match`".

```c filename=loop_body_proof_match_ensuring_inside_a_proof_if.c
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
verifying "loop_body_proof_match_ensuring_inside_a_proof_if.c";

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
            if i < 5 {
                match c.model ensuring {
                    owns c: cell(node);
                } {
                    Sign::Neg(value) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Neg(value) });
                    },
                    Sign::Pos(value) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Pos(value) });
                    },
                }
                match c.model {
                    Sign::Neg(w) => {
                        step();
                    },
                    Sign::Pos(w) => {
                        step();
                    },
                }
            } else {
                match c.model ensuring {
                    owns c: cell(node);
                } {
                    Sign::Neg(value2) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Neg(value2) });
                    },
                    Sign::Pos(value2) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Pos(value2) });
                    },
                }
                match c.model {
                    Sign::Neg(w2) => {
                        step();
                    },
                    Sign::Pos(w2) => {
                        step();
                    },
                }
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
