# A read through an arm identity is not the read through the parameter after a store

## Violated invariant

Two reads of one address at one program point are one value. With `p == id`
proved, `id->field` and `p->field` name the same cell, and the proof can state
that before any store. After one store to a different, separately owned
object, `simp()` can no longer prove it, for any field of the node, although
`p == id` is still provable and `p->field == at(m, p->field)` is too.

Reproduced on `12a167a48`. Save the C as `spelling.c` beside the sidecar:

```c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p, struct node *q) { q->tag = 1; }
```

```click
verifying "spelling.c";
spec enum Tree { Empty, Node(struct node*, Tree, Tree) }
resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, lm, rm) => {
            owns &p->left;
            owns &p->right;
            owns &p->tag;
            owns left: tree(p->left);
            owns right: tree(p->right);
            fact p != 0;
            fact p == id;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}
void roundtrip(struct node* p, struct node* q) {
    owns t: tree(p);
    owns &q->tag;
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            step();
            have id->right == p->right by { simp(); }
            let t = fold(tree(p), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
            execute();
            simp();
        },
    }
}
```

The `have` fails with ``could not establish `id->right == p->right` ``. The
same line with `left` (offset 0) or `tag` (an `int`) fails the same way.
Moved above `step()`, the `have` is accepted, and without it the proof
verifies.

A related form names the cause in its diagnostic: with `mark m;` before the
`step()`, `have id->right == at(m, id->right) by { simp(); }` fails with "the
store to `q[4]` may have written it, and nothing tells that address apart from
this read", while `have p->right == at(m, p->right)` is accepted. The likely
cause, inferred from that diagnostic and not traced in the code: the read
spelled through `id` is not carried to the owned cell filed under `p`, so the
ownership that frames the store away from `p->right` is never consulted for
it.

A fold's child argument had the same symptom for a different, traced reason
(the cached-run slot lookup in `run_slots_equal_to_load` was keyed by the
exact aliased pointer), and that is fixed in its own change. That fix was
checked not to change this bug: every result above is the same with and
without it. The symptom was recorded for the rbtree proof as "Pointer
spellings across a write or a fold" in `issues/rbtree-example.md`.

## Intended regression

The sidecar above as a passing mdtest, with the `have` for `right`, `left`,
and `tag`, and with the `at(m, ...)` form through `id`. Negatives that must
stay refused: the same `have` after `p->right = 0` compared against the
unfold-time child, and the store through a `q` the contract states equal to
`p`.

## Acceptance criteria

- After a store that ownership keeps apart from the node, a logical read
  through a pointer the context proves equal to the owning spelling, at any
  constant field offset, is the read through the owning spelling, and frames
  across that store exactly as the owning spelling does.
- The answer comes from the trusted equality graph's class relation or an
  index keyed by it, with work proportional to the access; no search of
  ownership frames, older snapshots, or spellings, and no history walk in
  equality queries.
- A store that may alias the cell still defeats both spellings alike.
