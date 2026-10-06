# A proof `match` over three constructors rejoins its arms

A `match` over more than two constructors is split pairwise, and each split
rejoins. Every arm leaves the state as it found it and proves the same fact,
so the three arms become one state: the statements after the `match` are
checked once, and the fact all three arms proved is still held.

```c filename=proof_match_three_arms_rejoin.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_three_arms_rejoin.c";

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
} by {
    step();
    match c.model {
        Sign::Neg(value) => {
            have node != 0 by { assumption(); }
        },
        Sign::Zero(value) => {
            have node != 0 by { assumption(); }
        },
        Sign::Pos(value) => {
            have node != 0 by { assumption(); }
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
