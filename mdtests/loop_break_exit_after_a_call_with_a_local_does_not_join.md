# An exit that called a function with a local does not join one that did not

`paint` leaves its `while (true)` by a `break` on both paths, and both paths
leave `p->shade` holding 0. One path stores the 0 itself; the other calls
`repaint`, which declares a local.

This is a pinned gap, not intended behaviour: the loop is refused with `loop
exits reach different states, so they have no common successor: memory`. The
two exits hold the same cells and own the same resources. They differ in what
the path remembers about automatic storage:

- the calling path's memory records that `repaint`'s `next` has ended (a
  tombstone for its block) and carries the forget mark that retiring the
  block's cell left;
- the calling path's state has taken one identity from the counter that names
  re-entered declarations, and the other path has not.

None of that is a layout of the same state, so the join's comparison, which
looks through the cell cache's layout and nothing else
([`loop_break_exit_join_compares_cells_not_their_cache.md`](loop_break_exit_join_compares_cells_not_their_cache.md)),
rightly keeps them apart. Joining them needs a rule for each component, which
`bugs/loop-exits-after-different-calls-do-not-join.md` sets out. The unchanged
Linux `__rb_insert` meets this: its rotation exits call
`__rb_rotate_set_parents`, which declares `parent`, and its early exits do
not.

```c filename=paint_through_helper.c
struct node { int32 shade; };

static void repaint(struct node* p) {
    int32 next = 0;
    p->shade = next;
}

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            repaint(p);
            break;
        } else {
            p->shade = 0;
            break;
        }
    }
}
```

```click
verifying "paint_through_helper.c";

void repaint(struct node* p) {
    owns p->shade;
    ensures p->shade == 0;
} by auto;

void paint(struct node* p, int32 flag) {
    owns p->shade;
    ensures p->shade == 0;
} by {
    loop {
        decreases 0;
        owns p->shade;

        preserve by {
            if flag == 0 {
                step();
                step();
                step();
            } else {
                step();
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
fail: loop exits reach different states, so they have no common successor: memory
```
