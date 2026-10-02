# The exit join does not depend on the order the exits folded their binders in

`inspect` carries two instances through a `while (true)` whose two `break`s do
different amounts of work. One exit opens `a` to read its cell and folds it
back; the other leaves both instances exactly as the head handed them over.
Both exits hold the same two instances with the same models.

The join used to refuse this loop with `loop exits reach different states, so
they have no common successor: resource ownership`. Folding an instance seats
it after everything the path already held, so the first exit held `b` then `a`
and the second held `a` then `b`, and the residual check compared the two
resource contexts position by position. A resource context is a multiset: where
a path last folded a binder is not a component of its state. The check now
re-seats each exit's own binder instances the way it already re-seats the
successor's, so the exits are compared by what they hold.

This is the shape of an ascent that leaves by more than one `break`: the exit
at the root has no frame to open, and an exit below the root unfolds and
refolds its frame to read the parent's link. The unchanged Linux `rb_next`
ascent is the first proof that needed it.
[`loop_break_exit_join_sets_aside_unshared_cells.md`](loop_break_exit_join_sets_aside_unshared_cells.md)
is the companion for the cells such an exit read.

```c filename=two_cells.c
struct node { int32 shade; };

int32 inspect(struct node* p, struct node* q, int32 flag) {
    int32 seen = 0;
    while (true) {
        if (flag == 0) {
            seen = p->shade;
            break;
        } else {
            break;
        }
    }
    return 0;
}
```

```click
verifying "two_cells.c";

resource shaded(p: struct node*) {
    field shade: int32;
    owns p->shade;
    fact p->shade == shade;
}

int32 inspect(struct node* p, struct node* q, int32 flag) {
    owns a: shaded(p);
    owns b: shaded(q);
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases 0;
        owns a: shaded(p);
        owns b: shaded(q);
        invariant a.shade == old(a.shade);

        initialize by simp;
        preserve by {
            if flag == 0 {
                unfold(a);
                step();
                step();
                let a = fold(shaded(p), { shade: old(a.shade) });
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
