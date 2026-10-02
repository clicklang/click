# An exit may have read a cell the first exit never opened

`inspect` leaves its `while (true)` by a `break` on every path. When `p` is
null the instance is `Cell::Missing` and owns nothing; otherwise the body
unfolds the instance, reads the cell the selected arm owns, and folds it back.
The resource keys that cell by the model's own payload, `identity->shade`, so
only the paths that open the instance ever hold a value for it.

The join describes one successor for all the exits. A cell the successor holds
and some exit does not is dropped from the successor: it is knowledge the
successor cannot claim. The opposite case used to be refused. The successor is
built from the first exit, so a later exit that had opened an instance the
first one left folded held a cell the successor never had, the residual check
found the two memories different, and the loop was refused with `loop exits
reach different states, so they have no common successor: memory`. Whether a
loop verified therefore depended on which exit the proof happened to write
first. A cell only some exit holds is now set aside on that exit's side before
the comparison, exactly as a dropped cell is: the successor still does not
claim it, and nothing else about the exit is relaxed.

The ownership the exits hand back is unchanged by this: each exit still has to
hold every declared binder, and a cell the exits *wrote* differently is still
abstracted through a binder or refused by name
([`loop_break_exit_unowned_cell_rejected.md`](loop_break_exit_unowned_cell_rejected.md)).
[`loop_break_exit_join_ignores_fold_order.md`](loop_break_exit_join_ignores_fold_order.md)
is the companion for the order the exits folded their binders in.

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
} by {
    step();
    step();
    loop {
        decreases 0;
        owns x: cell_at(p);
        invariant seen == 0;

        initialize by simp;
        preserve by {
            match x.model {
                Cell::Missing => {
                    unfold(x);
                    let x = fold(cell_at(p), { model: Cell::Missing });
                    step();
                    step();
                },
                Cell::Red(identity) => {
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Red(identity) });
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
pass
```
