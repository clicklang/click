# Linux rbtree erase

`rbtree_erase_augmented.click` verifies the unchanged Linux
`__rb_erase_augmented` under one general contract: any node of a red-black,
parent-consistent tree, at any position. It consumes the node's subtree
`rb_at(node)` and its context `ctx_at(node, root)`, and returns the detached
node's fields and an `erase_out(root, result)` outcome resource. A
`Balanced(t)` outcome owns the whole balanced tree `t`, with a null return;
a `Deficit(c)` outcome owns a context `c` missing one black level, with the
returned node as the parent where color repair must begin. The contract states
the exact outcome (`erase_outcome`, which follows the C's decision sequence),
its red-black and parent-consistency invariants, that its tree is the old
context plugged with `erase_splice` of the old subtree, and that the splice
keeps the old left and right in-order contents.

The proof has one arm per C exit: a leaf (red, black, or the sole root), a
left-only or right-only child, an immediate successor (red leaf, black leaf,
or one with a child), and a deeper successor (black leaf, or not). The C
executes once; each exit folds its outcome resource after the C returns.
Arms step the verified `__rb_change_child` contract, so the root and nonroot
positions share one proof. The deeper-successor exits run the unchanged
descent loop over the shared spine resources.

`rbtree_erase_general_wrapper.click` imports it and the general color-repair
proof and verifies the unchanged `rb_erase` under the same precondition. It
matches on the outcome and calls `____rb_erase_color` only for a deficit. It
returns the detached node and a balanced, parent-consistent root whose
in-order contents are the old context's with the node removed.

These two contracts replace 16 per-case sidecars: the `rb_erase` wrappers and
splice contracts for each exit and position, and the three older root and
leaf increments. Each is subsumed by the general contracts, so they were
retired ([design/proof-reuse.md](../../design/proof-reuse.md#r2-one-general-contract-per-function));
their history is in [the rbtree issue](../../issues/rbtree-example.md) and
in Git. Their mutation checks are nightly checks in `tests/examples.rs` that
the general unlink refuses each of the 25 distinct C mutations. A mutation
that deleted a statement is now a same-length replacement, so the proof's
statement positions still name the same statements. Their parent-link
mutations of the inlined helper are the `rbtree_change_child.click` checks.

`rbtree_change_child.click` verifies the shared C parent-link replacement
helper for root, left-child, and right-child links. Its contract retargets an
owned context while preserving its exact model and the old node's tag. Holding
that tag separates the old node from a nonempty sibling. Three mutation checks
reject a missing update on each link. Every exit of the general unlink steps
this contract to transfer the context.

Chunk 11 of [the rbtree issue](../../issues/rbtree-example.md) (deletion
at any position, all immediate and deeper-successor exits) is the general
unlink above. Erase-color repair, chunks 12–13, follows.

`rbtree_erase_color_flips_red_all.click` verifies the unchanged pinned
`____rb_erase_color` (chunks 12 and 13) under its general precondition: a
context missing one black level, with consistent parents. It covers
color-flip propagation followed by cases 1/2, 1/4, or 1/3/4, and the
black-sibling rotations, in both directions with nonempty focus and rotation
subtrees. The exact result, parent links, red-black invariants, and in-order
contents are preserved. A structural context proof derives case coverage from
the black-deficit invariant, so callers need no case selector.

The proof was developed through 22 per-case increments, from a single
first-iteration color flip to propagated red-sibling rotations. The general
proof subsumes every one of them, so they were retired
([design/proof-reuse.md](../../design/proof-reuse.md#r1-retire-superseded-increments-process));
their history is in [the rbtree issue](../../issues/rbtree-example.md) and in
Git. Each of the 39 distinct C mutations their tests pinned (a missing or
wrong link, parent, color, or cursor write) is now a nightly check in
`tests/examples.rs` that the general proof refuses.

`rbtree_rotate_set_parents.click` verifies the rotation helper's incoming-link
replacement at the root or either parent link. It copies the original packed
word to the new root, reparents and recolors the old root, and preserves the
exact outer context. All 35 expansion-audit sites pass. This supplies the
shared parent-update step for the remaining rotations.

`rbtree_set_parent.click` verifies the parent update for a nonempty subtree
of either color, preserving both child models. All 11 audit sites pass;
two mutations reject a lost color bit and an incorrect parent.

`rbtree_erase_leaf_wrapper.click` is the leaf-only `__rb_erase_augmented`
and `rb_erase` contracts the general ones subsume. It stays because
`examples/rbtree-augmented/rbtree_erase_leaf.click` imports its leaf unlink,
whose outputs (an empty hole and the remaining context) that proof consumes.

`rbtree_erase_callbacks.click` checks the shared dummy callbacks and their
refinements. The repair proof and the general unlink import the existing
`rbtree_change_child.click` parent-link contract. Every module is verified
separately; importing a contract does not rerun its proof.

`rb_erase.c` includes the existing unchanged splice and repair extracts and adds
the dummy callbacks, const table, and `rb_erase` definition verbatim from pinned
`lib/rbtree.c`. All helper bodies and callback refinements are checked in this
combined sidecar.

The callback contracts describe the non-augmented case: callbacks cannot
mutate tree fields or require augmentation metadata. The borrowed table is
separated from fields the C may write. Metadata-carrying callbacks remain
chunk 14.

The input is extracted from `include/linux/rbtree_augmented.h` inside
[`input-closure.tar.gz`](../../integrations/linux-rbtree/input-closure.tar.gz).
The `rb_augment_callbacks` declaration and `__rb_erase_augmented` definition,
including comments, are verbatim. The header shim reuses the insertion
example's supported rbtree types and macros and spells the pinned
`__rb_parent` mask. This is not yet the complete pinned translation-unit
integration planned in chunks 21–24. The source is GPL-2.0-or-later.

The full erase project runs in the nightly example suite. Run `click verify examples/rbtree-erase` and
`click verify examples/rbtree-model`. The latter checks the imported pure
root-deletion and successor-splice theorems independently. The pinned-source
checks run in the ordinary gate; the mutation checks and the re-verification
of the general unlink's expanded final closers run nightly.

The shared `rbtree_spine_model.click` and `rbtree_spine_resources.click`
modules define the left-only descent path. Its anchor owns only the original
right child's left link, leaving that child's parent/color and right link
available for transplant. The terminating `refold_erase_spine` tactic rebuilds
a balanced subtree; `graft_erase_spine` instead keeps an empty deficit hole and
joins the path to its new outer context. Both preserve exact models.

The spine lemmas connect minimum identity, minimum parent, and minimum context
to the original subtree, commute minimum removal with path reconstruction, and
recover each frame's parent link from whole-tree parent consistency. The
general unlink's deeper-successor exits use these shared lemmas after the
unchanged descent loop.
