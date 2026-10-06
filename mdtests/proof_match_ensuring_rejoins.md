# A proof `match` rejoins arms that refold different constructors

Each arm unfolds the cell and refolds it with its own constructor, so the
arms end holding a cell with different models. `ensuring` names the cell the
rejoined proof holds and states what both arms establish about its model; the
statements after the `match` are then checked once.

```c filename=proof_match_ensuring_rejoins.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_ensuring_rejoins.c";

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

int32 peek(struct cell* node) {
    requires node != 0;
    owns c: cell(node);
    ensures result == 0;
    ensures c.model == old(c.model);
} by {
    step();
    match c.model ensuring {
        owns c: cell(node);
        fact c.model == old(c.model);
    } {
        Sign::Neg(value) => {
            have Sign::Neg(value) == old(c.model) by { simp(); }
            unfold(c);
            let c = fold(cell(node), { model: Sign::Neg(value) });
            have c.model == old(c.model) by { simp(); }
        },
        Sign::Pos(value) => {
            have Sign::Pos(value) == old(c.model) by { simp(); }
            unfold(c);
            let c = fold(cell(node), { model: Sign::Pos(value) });
            have c.model == old(c.model) by { simp(); }
        },
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
