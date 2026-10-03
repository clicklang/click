# A fact every `break` exit states about a binder's model is kept after the loop

`inspect` leaves its `while (true)` by a `break` on every path, and every exit
states the same thing in the same words: `x.model == old(x.model)`. One exit
holds the instance at the arm's field-free constructor; the other two unfolded
it, read its cell, and folded it back at a constructor that carries the arm's
binding. The binder's model is therefore a different *term* at each exit,
although each exit proved it is the entry model.

The join gives a component the exits disagree about one fresh name, and each
exit contributes, as its own disjunct, the equation pinning that name to what
the exit held. Reading the common claim off that disjunction with `cases`
needs every disjunct spelled, and two of them name a constructor whose field
is an arm binding no proof after the loop can write.

So the join also restates. For each exit, every fact that mentions the exit's
value for a renamed binder is restated with that value replaced by the
successor's name, as a term: `Cell::Missing == old(x.model)` at one exit and
`Cell::Red(identity) == old(x.model)` at another both become `x.model ==
old(x.model)` about the successor. On each exit's path the name equals the
exit's value, so the restated fact holds there; a fact every exit restates
identically holds on every path into the successor and is kept as an ordinary
fact. Nothing is searched for and nothing is proved again.

A fact some exit does not state is not kept
([`loop_break_exit_fact_one_exit_does_not_state_is_dropped.md`](loop_break_exit_fact_one_exit_does_not_state_is_dropped.md)),
and neither is one that is about another binder
([`loop_break_exit_fact_about_another_binder_is_not_restated.md`](loop_break_exit_fact_about_another_binder_is_not_restated.md)).

```c filename=one_cell.c
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
verifying "one_cell.c";

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
                    have Cell::Black(identity) == old(x.model) by {
                        rewrite(Cell::Black(identity) == x.model);
                        assumption();
                    }
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Black(identity) });
                    have x.model == old(x.model) by {
                        rewrite(x.model == Cell::Black(identity));
                        assumption();
                    }
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
pass
```
