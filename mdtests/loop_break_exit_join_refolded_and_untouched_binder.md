# An exit that refolded a binder joins one that never opened it

`paint` leaves its `while (true)` by a `break` on both paths. One path opens
the binder, writes its cell and folds it back; the other never touches it.

They used to be refused with `loop exits reach different states, so they have
no common successor: resource ownership`. Opening the binder leaves the path a
second copy of a view of the cell that it already held, and folding does not
take it back. A view held twice is one view: the resource algebra merges the
pair, and the kernel already compares an unfolded body with its expected one
in that normalized form. The join's last check now compares the exits'
resources in the same form. Nothing owned is merged away by it, so an exit
that holds no instance for a declared binder
([`loop_break_exit_missing_binder_rejected.md`](loop_break_exit_missing_binder_rejected.md))
is still refused.

The function claims nothing about the colour after the loop. The untouched
exit describes its binder by the model the loop head gave it, a name no proof
after the loop can spell, so the exported disjunction cannot be named for
`cases` here. What this fixture pins is that the loop rule itself certifies:
the function still has to hand back `painted(p)` after it.

```c filename=paint_or_skip.c
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
verifying "paint_or_skip.c";

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
} by {
    loop {
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        preserve by {
            if flag == 0 {
                unfold(c);
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                step();
            } else {
                step();
                step();
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
