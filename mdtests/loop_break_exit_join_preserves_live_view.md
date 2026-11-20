# A loop-exit join separates the differing cell from a live view

The break exits write different values into the cell owned by the loop's
binder. Their join abstracts that cell while retaining the view, which the
function reads after the loop.

```c filename=paint_with_view.c
struct node { int32 shade; };

int32 paint(struct node* p, const int32* q, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            break;
        } else {
            p->shade = 1;
            break;
        }
    }
    return q[0];
}
```

```click
verifying "paint_with_view.c";

spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

int32 paint(struct node* p, const int32* q, int32 flag) {
    owns c: painted(p);
    views q[0..1];
    requires separate(memory(p->shade), memory(q[0..1]));
    requires c.color == Color::Black;
    ensures c.color == Color::Red or c.color == Color::Black;
    ensures result == q[0];
} by {
    have separate(memory(p->shade), memory(q[0..1])) by { known(); }
    have contains(memory(p->shade), memory((p as (uint8*))[0..4])) by { normalize(); }
    have contains(memory(q[0..1]), memory(q[0..1])) by { normalize(); }
    have separate(memory((p as (uint8*))[0..4]), memory(q[0..1])) by {
        apply(click::separation::separate_restrict(memory(p->shade), memory(q[0..1]), memory((p as (uint8*))[0..4]), memory(q[0..1]))) using {
            separate(memory(p->shade), memory(q[0..1]));
            contains(memory(p->shade), memory((p as (uint8*))[0..4]));
            contains(memory(q[0..1]), memory(q[0..1]));
        };
    }
    loop {
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        maintain by {
            unfold(c);
            if flag == 0 {
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                step();
            } else {
                step();
                step();
                let c = fold(painted(p), { color: Color::Black });
                step();
            }
        }
    }
    step();
    have c.color == Color::Red or c.color == Color::Black by {
        cases {
            (flag == 0 and c.color == Color::Red and p->shade == 0) => {
                solve();
            }
            (c.color == Color::Black and p->shade == 1) => {
                solve();
            }
        }
    }
    solve();
}
```

```expect
pass
```
