# Exits that hold the same cells join, however the cell cache keeps them

`paint` leaves its `while (true)` by a `break` on both paths. One path writes
the cell the binder owns; the other only opens the binder and closes it again.
After the join abstracts the cell the two paths wrote differently, the
successor and each exit hold the same cells with the same values.

They used to be refused all the same, with `loop exits reach different states,
so they have no common successor: memory`. Unfolding the binder seeds its cell
as a one-slot run. The path that writes the cell retires that run and holds a
concrete cell; the path that does not write keeps the live slot. The join's
last check compared the two memories structurally, so one cell held two ways
was two memories. A run is exactly the cells it stands for, so the check now
compares the cells: the same pointers with the same values. Everything else
about a memory is compared as before, which is why a write no binder describes
([`loop_break_exit_unowned_cell_rejected.md`](loop_break_exit_unowned_cell_rejected.md))
is still refused.

The claim after the loop is proved from the exported disjunction, so both
exits reach the successor.

The proof opens the joined resource in each model case to obtain its current
cell-value fact, then exports the full disjunction explicitly. It does not
recover that fact by registering a read against the joined memory cache.

```c filename=paint_or_leave.c
struct node { int32 shade; };

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            break;
        } else {
            break;
        }
    }
}
```

```click
verifying "paint_or_leave.c";

spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

void paint(struct node* p, int32 flag) {
    owns c: painted(p);
    requires c.color == Color::Black;
    ensures c.color == Color::Red or c.color == Color::Black;
} by {
    loop {
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        maintain by {
            if flag == 0 {
                unfold(c);
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                step();
            } else {
                unfold(c);
                step();
                let c = fold(painted(p), { color: Color::Black });
                step();
            }
        }
    }
    have flag == 0 or c.color == Color::Black by {
        cases {
            (flag == 0 and c.color == Color::Red) => { solve(); }
            (c.color == Color::Black) => { solve(); }
        }
    }
    match c.color ensuring {
        owns c: painted(p);
        fact (flag == 0 and c.color == Color::Red and p->shade == 0) or (p->shade == 1 and c.color == Color::Black);
    } {
        Color::Red => {
            have flag == 0 by {
                cases {
                    (flag == 0) => { known(); }
                    (c.color == Color::Black) => { solve(); }
                }
            }
            unfold(c);
            let c = fold(painted(p), { color: Color::Red });
            have (flag == 0 and c.color == Color::Red and p->shade == 0) or (p->shade == 1 and c.color == Color::Black);
        },
        Color::Black => {
            unfold(c);
            let c = fold(painted(p), { color: Color::Black });
            have (flag == 0 and c.color == Color::Red and p->shade == 0) or (p->shade == 1 and c.color == Color::Black);
        },
    }
    have c.color == Color::Red or c.color == Color::Black by {
        cases {
            (flag == 0 and c.color == Color::Red and p->shade == 0) => {
                solve();
            }
            (p->shade == 1 and c.color == Color::Black) => {
                solve();
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
