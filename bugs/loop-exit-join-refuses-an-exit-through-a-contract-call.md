# A loop exit through a contract call does not join one that stores directly

## Violated invariant

Two `break` exits of a loop that leave the same cells holding the same values,
under the same owned resources, join into one successor. When one exit reaches
that state by calling a function through its verified contract and the other
by storing directly, the join is refused:

```
loop exits reach different states, so they have no common successor: memory, resource ownership
```

Reduction (an ordinary, non-`static` callee, so this is not specific to inline
helpers; it predates inline helpers applying their contracts):

```c
struct node { int32 shade; };

void repaint(struct node* p) {
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
            if flag == 0 { step(); step(); step(); }
            else { step(); step(); step(); }
        }
    }
    step();
    simp();
}
```

Without `repaint`'s contract, the body runs at the call site and the same
loop verifies (`mdtests/loop_break_exit_after_a_call_with_a_local_joins.md`).
The contract call presumably hands the owned cell back under a different
memory snapshot or resource identity than the direct store keeps. Not
investigated further.

The unchanged Linux `__rb_insert` has this shape once its inline helpers
apply their contracts: rotation exits call helpers, early exits do not.

## Intended regression

The reduction above as a passing mdtest. Also the variant where both exits call
`repaint`, and one where the exits leave different values, which must still be
refused.

## Acceptance criteria

- Exits that agree on cells, values, and owned resources join, whether they got
  there through a contract call or a direct store.
- Exits that disagree are still refused by name.
- `scripts/check.sh` passes.
