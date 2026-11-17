# A fold owes no body fact that holds without facts

Refolding `cell_at(c)` with its old model makes the body fact `p == identity`
read `c == c`. That clause holds without any fact, so the fold does not raise
it as a prerequisite for a smart step to prove; an expansion writes no
`requires` entry for it.

```c filename=a_fold_owes_no_body_fact_that_holds_without_facts.c
struct cell { int value; };
int read(struct cell *c) { return c->value; }
```

```click
verifying "a_fold_owes_no_body_fact_that_holds_without_facts.c";

spec enum Cell { At(struct cell*, int) }

resource cell_at(p: struct cell*) {
    field model: Cell;
    match model {
        Cell::At(identity, value) => {
            owns p->value;
            fact p == identity;
            fact p->value == value;
        },
    }
}

int read(struct cell* c) {
    owns root: cell_at(c);
    requires root.model == Cell::At(c, 7);
    ensures result == 7;
    ensures root.model == old(root.model);
} by {
    unfold(root);
    step_until(function.exit);
    let root = fold(cell_at(c), { model: old(root.model) });
    solve();
}
```

```expect
pass
```
