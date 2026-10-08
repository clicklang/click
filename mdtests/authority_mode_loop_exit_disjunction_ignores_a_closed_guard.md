# A loop exit disjunction ignores a closed true conjunct in authority mode

`paint` leaves its `while (true)` by a `break` on both paths, and the proof
after the loop reasons by cases on the exported disjunction
`(flag == 0 and c.color == Red and p->shade == 0) or (p->shade == 1 and
c.color == Black)`, as `loop_break_exit_join_compares_cells_not_their_cache.md`
does under legacy semantics.

Under authority semantics one exit also stated the closed fact `true == true`.
The join orders the disjuncts by how many facts each path states and then
drops a conjunct an earlier disjunct contradicts. The extra fact reordered
the exits, so the exported disjunction was not the one the proof names. A
closed true conjunct says nothing about its path and is no longer counted.

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

```click resource_semantics=authority
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

        preserve by {
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
    step();
    have c.color == Color::Red or c.color == Color::Black by {
        cases {
            (flag == 0 and c.color == Color::Red and p->shade == 0) => {
                simp();
            }
            (p->shade == 1 and c.color == Color::Black) => {
                simp();
            }
        }
    }
    simp();
}
```

```expect
pass
```
