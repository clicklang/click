# What every `break` exit states about a binder's model is not available after the loop

`inspect` leaves its `while (true)` by a `break` on every path, and every exit
states the same thing in the same words: `x.model == old(x.model)`. One exit
holds the instance at the arm's field-free constructor; the other two unfolded
it, read its cell, and folded it back at a constructor that carries the arm's
binding. The binder's model is therefore a different *term* at each exit,
although each exit proved it is the entry model.

The join gives a component the exits disagree about one fresh name and has each
exit contribute, as its own disjunct, the equation pinning that name to what
the exit held. What an exit stated about its own model is not restated about
the fresh name, so the common claim is not a fact after the loop. Reading it
off the exported disjunction with `cases`, as
[`loop_break_exit_binder_model_join.md`](loop_break_exit_binder_model_join.md)
reads a colour back, needs every disjunct spelled, and here two of them name a
constructor whose field is an arm binding no proof after the loop can write.
The claim every exit proved is out of reach.

This is the open "Loop exits" finding recorded in
[`issues/rbtree-example.md`](../issues/rbtree-example.md), reduced. It is what
stops the unchanged Linux `rb_next` after its ascent loop: every exit states
`plug(c.model, t.model) == plug(old(c.model), old(t.model))`, and the function
needs it to describe the node it returns ([`rb_next.md`](rb_next.md)). The
fixture pins the refusal; it becomes a positive when the join restates each
exit's facts about the names it introduces.

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
fail: `ensures x.model == old(x.model)` failed
```
