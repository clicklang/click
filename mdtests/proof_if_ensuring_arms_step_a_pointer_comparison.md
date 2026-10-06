# Arms that step a decided pointer comparison rejoin

Each arm of the proof `if` opens the cell, steps the C `if (p == q)`, whose
guard is false because the proof holds both cells, steps the empty arm that
guard selects, and stores through `p`. The arms refold the cell with
different models, so they rejoin through `ensuring`.

The join re-walks each arm's recorded steps from the split. Three things in
these arms are easy for that walk to get wrong:

- the comparison's theorem assumes the state held both pointers' owners,
  which is read off the state the walk has reached, not off the arm's final
  facts, where the cell is folded again;
- the stepped empty arm is a `skip` that consumes no source, because the
  source kept after a decided guard does not include it;
- the arms forgot cached values from different memories on the way, which
  must not make their joined memories differ.

```c filename=proof_if_ensuring_arms_step_a_pointer_comparison.c
struct cell { int32 value; };

int32 pick(struct cell *p, struct cell *q, int32 x) {
    int32 a;
    a = 0;
    if (p == q) {
        a = 1;
    }
    p->value = a;
    return a;
}
```

```click
verifying "proof_if_ensuring_arms_step_a_pointer_comparison.c";

resource cell(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 pick(struct cell* p, struct cell* q, int32 x) {
    requires p != 0;
    requires q != 0;
    owns c: cell(p);
    owns d: cell(q);
    ensures result == 0;
} by {
    step();
    step();
    unfold(d);
    if x <= 0 ensuring {
        owns c: cell(p);
        fact a == 0;
    } then {
        unfold(c);
        step();
        step();
        step();
        let c = fold(cell(p), { model: 0 });
    } else {
        unfold(c);
        step();
        step();
        step();
        let c = fold(cell(p), { model: p->value });
    }
    let d = fold(cell(q), { model: q->value });
    step();
    simp();
}
```

```expect
pass
```
