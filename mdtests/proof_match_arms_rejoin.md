# A proof `match` followed by tactics rejoins its arms

The `match` opens the cell's model between two C statements. Each arm reasons
about its own constructor and leaves the state as it found it, so the arms
rejoin: the statements after the `match` are checked once, from one state.
The constructor of each arm, and its fields, do not survive the join.

```c filename=proof_match_arms_rejoin.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_arms_rejoin.c";

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
} by {
    step();
    match c.model {
        Sign::Neg(value) => {
            have value < 0 or value >= 0;
        },
        Sign::Pos(value) => {
            have value < 0 or value >= 0;
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
