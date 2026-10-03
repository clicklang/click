# Linux rbtree insertion

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture; `tests/examples.rs` pins both
files by SHA-256.

`rbtree_insert.click` proves the Linux insert fixup, `__rb_insert`, end to end.
It takes the context and the red subtree at the inserted node
(`ctx_at(node, root)` and `rb_at(node)`, with the frame-level red-black,
order, and parent-link facts the case theorems use) and produces the fixed-up
tree as `rb_tree_at(root)`: a context and a subtree at some focus node, whose
`focus_tree` is red-black with a black root, has the entry's in-order
sequence, and has consistent parent links.

The tree is produced at a focus rather than at `root->rb_node` because the
fixup stops wherever its rotation or recolouring finishes, with an arbitrary
number of context frames above that point. Folding them back into one subtree
at the root would take one `fold` per frame, which a finite proof cannot
write, and the C has no loop that climbs back up. The packaging owns the same
cells, including `root->rb_node` in the `Top` frame, and states the same whole
tree through `plug`.

The proof covers `initialize`, the root-blackening and black-parent `break`s,
the uncle-red `continue` on all four frame combinations, and all 96 rotation
`break`s: case 3 on the outer frames and case 2 then case 3 on the inner
ones, split on the uncle, the rotated nodes' children, and the
great-grandparent's frame. Every `break` states the three whole-tree facts
about `plug(c.model, t.model)`, so they survive the loop's exit join, and the
post-loop proof folds the two binders into `rb_tree_at(root)`.

`rb_insert_color` itself has no proof here. It calls `__rb_insert`, a
`static __always_inline` helper, and Click executes an inline helper's body at
each call site instead of applying its contract, so a proof of
`rb_insert_color` would have to execute the fixup loop again without its
invariants. See `bugs/inline-helper-symbolic-loop-call-runs-away.md`.

`tests/examples.rs` also checks that the proof refuses a copy of the C whose
root case skips `rb_set_parent_color(node, NULL, RB_BLACK)`.

Run it with:

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

The sidecar imports the model from the sibling project, so its project root is
`examples`, the nearest directory holding both. `--trace-to` reaches the
tactics inside the fixup's proof `match` arms and its `preserve` body:

```sh
click verify --trace-proof __rb_insert --trace-to LINE examples/rbtree-insert/rbtree_insert.click
```
