# An arm that contains a rejoined `match` rejoins in turn

Each arm of the proof `if` opens `p`'s slot, rejoins a `match` over `q`'s
cell around the first C statement, then steps the store and folds the slot
again. The arms fold the slot with differently spelled models, so the `if`
rejoins through its own `ensuring`.

The outer join re-walks each arm's recorded steps, and an arm's steps now
include the inner join. Two things about that are easy to get wrong:

- the steps after the inner join were proved under facts later than the ones
  the inner join left, so the walk keeps the arm's own final facts across it
  instead of falling back to the inner join's;
- the inner join's memory summary is a checked fact the outer join takes as
  it stands. A join's memory forgets values no arm wrote, so the summary
  cannot be derived a second time from the two memories it relates.

```c filename=proof_match_ensuring_nested_in_a_proof_if_ensuring.c
struct cell { int32 value; };

int32 bump(struct cell *p, struct cell *q, int32 x) {
    int32 a;
    a = q->value;
    p->value = 1;
    return 0;
}
```

```click
verifying "proof_match_ensuring_nested_in_a_proof_if_ensuring.c";

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

resource slot(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 bump(struct cell* p, struct cell* q, int32 x) {
    requires p != 0;
    requires q != 0;
    owns c: slot(p);
    owns d: cell(q);
    ensures result == 0;
} by {
    step();
    if x <= 0 ensuring {
        owns c: slot(p);
        owns d: cell(q);
    } then {
        unfold(c);
        match d.model ensuring {
            owns d: cell(q);
        } {
            Sign::Neg(value) => {
                unfold(d);
                step();
                let d = fold(cell(q), { model: Sign::Neg(value) });
            },
            Sign::Pos(value) => {
                unfold(d);
                step();
                let d = fold(cell(q), { model: Sign::Pos(value) });
            },
        }
        step();
        let c = fold(slot(p), { model: 1 });
    } else {
        unfold(c);
        match d.model ensuring {
            owns d: cell(q);
        } {
            Sign::Neg(low) => {
                unfold(d);
                step();
                let d = fold(cell(q), { model: Sign::Neg(low) });
            },
            Sign::Pos(high) => {
                unfold(d);
                step();
                let d = fold(cell(q), { model: Sign::Pos(high) });
            },
        }
        step();
        let c = fold(slot(p), { model: p->value });
    }
    step();
    simp();
}
```

```expect
pass
```
