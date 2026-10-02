# Loop `break` exits that reach the same state in a different representation do not join

## Violated invariant

A loop has one successor. `join_loop_exits` in `src/kernel/loops.rs`
abstracts what the exits disagree about (binder models, locals, cells written
differently) and then requires what is left to be equal
(`loop_exit_residual_difference`). That last comparison is `CState ==`, which
is structural, so exits that own the same resources and hold the same bytes
are refused when they differ only in how the state is represented:

1. **Cell cache shape.** One exit wrote a binder's cell and the other only
   unfolded and refolded it. The first holds the cell as a concrete cell, the
   second as a slot of the run the unfold seeded. `CellStore` equality compares
   the two maps separately, so the exits differ in "memory".
2. **Refold order.** Two binders refolded in a different order at two exits
   give the same resource facts in a different insertion order, and
   `ResourceContext` equality compares the ordered fact list, so the exits
   differ in "resource ownership".
3. **An untouched binder.** One exit never unfolds the binder and the other
   refolds it. The exits differ in "resource ownership" (the two contexts
   hold three resource facts against two).

Each is refused with `loop exits reach different states, so they have no
common successor: memory` (or `resource ownership`), with `false = true` as
the missing prerequisite. Nothing in the message says which exits differ or
in what.

This blocks the rbtree insert proof. With all 99 paths of `__rb_insert`'s
loop body written (3 early `break`s, 96 rotation `break`s, 4 `continue`s),
the loop rule is refused with `memory, resource ownership`: the rotation
exits hold the two binders in two different orders (case 3 folds the subtree
first, case 2 the context first), the three early exits in a third, and the
exits hold different sets of cached cells.
Reordering folds across a hundred leaves to match, where that is possible at
all, is proof bookkeeping the C does not ask for.

Reproduced on `940c789fd`. All three use this C header and resource:

```c
struct node { int32 shade; };
```

```click
spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

```

### 1. Cell cache shape (`memory`)

```c
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
                unfold(c);
                step();
                let c = fold(painted(p), { color: Color::Black });
                step();
            }
        }
    }
    step();
    simp();
}
```

### 2. Refold order (`resource ownership`)

```c
void paint(struct node* p, struct node* q, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            q->shade = 0;
            break;
        } else {
            p->shade = 1;
            q->shade = 1;
            break;
        }
    }
}
```

```click
void paint(struct node* p, struct node* q, int32 flag) {
    owns c: painted(p);
    owns d: painted(q);
    requires c.color == Color::Black;
    requires d.color == Color::Black;
} by {
    loop {
        decreases 0;
        owns c: painted(p);
        owns d: painted(q);
        invariant c.color == Color::Black;
        invariant d.color == Color::Black;

        preserve by {
            unfold(c);
            unfold(d);
            if flag == 0 {
                step();
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                let d = fold(painted(q), { color: Color::Red });
                step();
            } else {
                step();
                step();
                step();
                let d = fold(painted(q), { color: Color::Black });
                let c = fold(painted(p), { color: Color::Black });
                step();
            }
        }
    }
    step();
    simp();
}
```

Folding `c` before `d` in both arms verifies.

### 3. An untouched binder (`resource ownership`)

The C of case 1, with the second arm not opening the binder:

```click
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

`mdtests/loop_break_exit_binder_model_join.md`, where both exits write the
cell and refold the one binder, verifies.

## Intended regression

The three sidecars above as passing mdtests beside
`loop_break_exit_binder_model_join.md`, each with a post-loop claim proved
from the exported disjunction, so the join is shown to export every exit.
Negatives that must stay refused: an exit that holds no instance for a
declared binder (`loop_break_exit_missing_binder_rejected.md`), an exit that
leaves a cell owned by no binder written differently
(`loop_break_exit_unowned_cell_rejected.md`), and exits that differ in an
allocation lifetime or in ownership outside the binders.

## Acceptance criteria

- Exits that hold the same owned resources and the same known cell values
  join, whatever order they were folded in and however the cell cache
  represents those values. A cached value only some exits hold is dropped from
  the successor, as the rule already does for the first exit's cells.
- The comparison is over the loop's binders and the cells and locals the
  exits disagree on, as the rule's cost note says; it does not scan unrelated
  state and it does not become an all-pairs comparison of exits.
- A real difference (ownership beyond the binders, allocation lifetimes, a
  cell no binder describes) is still refused, and the refusal names the exit
  and the component.
- `examples/rbtree-insert/rbtree_insert.frontier` gets past the loop rule.
