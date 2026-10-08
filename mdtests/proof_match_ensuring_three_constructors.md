# A proof `match` over three constructors rejoins through its interface

A `match` over more than two constructors is split pairwise. Each split
rejoins through the same `ensuring` interface, so the three arms become one
state and the statements after the `match` are checked once.

```c filename=proof_match_ensuring_three_constructors.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_ensuring_three_constructors.c";

spec enum Sign { Neg(int32), Zero(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Zero(value) => {
            owns p->value;
            fact p->value == value;
            fact value == 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value > 0;
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
            have Sign::Neg(value) == old(c.model);
            unfold(c);
            let c = fold(cell(node), { model: Sign::Neg(value) });
            have c.model == old(c.model);
        },
        Sign::Zero(value) => {
            have Sign::Zero(value) == old(c.model);
            unfold(c);
            let c = fold(cell(node), { model: Sign::Zero(value) });
            have c.model == old(c.model);
        },
        Sign::Pos(value) => {
            have Sign::Pos(value) == old(c.model);
            unfold(c);
            let c = fold(cell(node), { model: Sign::Pos(value) });
            have c.model == old(c.model);
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
