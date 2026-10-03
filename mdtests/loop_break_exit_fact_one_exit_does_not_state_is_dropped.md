# A fact one `break` exit does not state is not kept after the loop

The loop of
[`loop_break_exit_keeps_a_fact_every_exit_restates.md`](loop_break_exit_keeps_a_fact_every_exit_restates.md),
with one change: the `Cell::Black` exit folds its instance back and says
nothing about how the model it folded relates to the entry model. The other
two exits state `x.model == old(x.model)` exactly as before.

The join keeps a restated fact only when every exit restates it. Two exits out
of three is not every exit, so the claim is not a fact after the loop and the
contract's `ensures` is refused. That the claim happens to be true on the
silent path is beside the point: the join passes along what each exit checked
and proves nothing itself.

```c filename=one_cell_one_silent_exit.c
struct node { int32 shade; };

int32 inspect(struct node* p) {
    int32 seen = 0;
    while (true) {
        if (p == 0)
            break;
        seen = p->shade;
        break;
    }
    return 0;
}
```

```click
verifying "one_cell_one_silent_exit.c";

spec enum Cell {
    Missing,
    Red(struct node*),
    Black(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Red(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
        Cell::Black(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
    }
}

int32 inspect(struct node* p) {
    owns x: cell_at(p);
    ensures result == 0;
    ensures x.model == old(x.model);
} by {
    step();
    step();
    loop {
        decreases 0;
        owns x: cell_at(p);
        invariant x.model == old(x.model);

        preserve by {
            match x.model {
                Cell::Missing => {
                    have Cell::Missing == old(x.model) by {
                        rewrite(Cell::Missing == x.model);
                        assumption();
                    }
                    unfold(x);
                    let x = fold(cell_at(p), { model: Cell::Missing });
                    have x.model == old(x.model) by {
                        rewrite(x.model == Cell::Missing);
                        assumption();
                    }
                    step();
                    step();
                },
                Cell::Red(identity) => {
                    have Cell::Red(identity) == old(x.model) by {
                        rewrite(Cell::Red(identity) == x.model);
                        assumption();
                    }
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Red(identity) });
                    have x.model == old(x.model) by {
                        rewrite(x.model == Cell::Red(identity));
                        assumption();
                    }
                    step();
                },
                Cell::Black(identity) => {
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Black(identity) });
                    step();
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: `ensures x.model == old(x.model)` failed
```
