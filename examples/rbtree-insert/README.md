# Linux rbtree insertion frontier

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture.

`rbtree_insert.click` is the green project entry: it checks that the shared
model and unchanged C load together, but intentionally selects no insert
proof. `rbtree_insert.frontier` contains the full insert contract and current
proof attempt. The examples integration test selects that frontier separately
and requires its bounded diagnostic to remain at the first unfinished
black-uncle path (statement 52 of the loop body, `tmp = parent->rb_left`,
with 67 `break`s and 4 `continue`s complete). A passing import-only
entry therefore does not represent the insert proof as complete.

The proof so far covers `initialize`, the root-blackening and black-parent
`break`s, and the uncle-red `continue` on all four frame combinations: each
recolours the uncle, the parent, and the grandparent, refolds the three nodes
at their new models, and closes the loop's nine invariants and the two-frame
structural descent through `ctx_insert_case1_left_step` or
`ctx_insert_case1_right_step` from the shared model.

Case 3 on the left-left frames with a black uncle is complete on all sixteen
leaves, eight under a node uncle and eight under an empty one, which is
refolded as `RbTree::Empty` and otherwise reads the same: the proof splits on
the parent's other child (empty or a node,
since `if (tmp)` writes its parent word) and on the grandparent's own frame
(`Top`, `Left`, or `Right`, since `__rb_change_child` writes that frame's child
cell), steps through the rotation and the inline `__rb_rotate_set_parents`,
refolds the grandparent and the new frame at the rotated parent, and states
the three whole-tree facts the post-loop proof will read at the `break`
through `ctx_insert_case3_left_step`. Under a `Right` grandparent frame whose
other child is a node, that child is unfolded before the step, so that
`parent->rb_left == old` is decided, and refolded at its arm identity after
it. The right-right frames are the mirror image, sixteen leaves through
`ctx_insert_case3_right_step`.

The cursor-`Right`, grandparent-`Left` frames rotate at the parent first
(case 2) and then at the grandparent, on 32 leaves: the uncle, each of the
cursor's two children (each `if (tmp)` writes one's parent word), and the
great-grandparent's frame. The old parent and the grandparent are refolded as
the cursor's two red children, the cursor as the new black subtree root, and
the great-grandparent's frame at `node` as the loop's context;
`ctx_insert_case2_left_exit_step` states the whole-tree facts on that shape.
The mirrored cursor-`Left`, grandparent-`Right` frames, the body's end, the
post-loop proof, and `rb_insert_color` remain.

Run the normal full rbtree scope with:

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

Inspect the unfinished proof directly with:

```sh
click verify examples/rbtree-insert/rbtree_insert.frontier
click verify --trace-proof __rb_insert --trace-to LINE examples/rbtree-insert/rbtree_insert.frontier
```

The frontier imports the model from the sibling project, so its project root
is `examples`, the nearest directory holding both; `--trace-to` reaches the
tactics inside the fixup's proof `match` arms and its `preserve` body.
