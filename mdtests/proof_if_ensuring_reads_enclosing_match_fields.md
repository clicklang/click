# An `ensuring` block may name the fields of an enclosing `match` arm

The `if` sits inside the `Neg` arm of a proof `match`, where `value` is that
arm's field. Its `ensuring` block is written in the same scope as the `have`
goals around it, so it may name `value` too.

```c filename=proof_if_ensuring_reads_enclosing_match_fields.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_if_ensuring_reads_enclosing_match_fields.c";

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
            if value <= 0 ensuring {
                fact value <= 0 or value > 0;
            } then {
                have value <= 0 or value > 0;
            } else {
                have value <= 0 or value > 0;
            }
            step();
            step();
            simp();
        },
        Sign::Pos(value) => {
            step();
            step();
            simp();
        },
    }
}
```

```expect
pass
```
