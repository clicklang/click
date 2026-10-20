# rbtree-augmented's sized resources lack #1245's parent pointer fact

Soundness: incomplete. Existing checked proofs are refused; nothing false is
accepted.

#1245 (`2cee79c02`, pointer designation) added
`fact ((struct rb_node*)(p->__rb_parent_color & ~3)) == parent;` to `rb_at`
and `ctx_at` in `examples/rbtree/rbtree-model`, and made numeric word facts such as
`(old(*p) & ~3) == (uint64)parent` stop implying the pointer equality. The
parallel resources in `examples/rbtree/rbtree-augmented` (`sized_at` and the sized
context resources) never received the fact, so every fold of `rb_at` from a
sized node and every loop invariant stated as a pointer equality now fails.
These sidecars verified before #1245; rbtree-augmented is quarantined from
the gate (`tests/examples.rs`), so the merge queue did not run them.

On master `a69f1cff2`:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-augmented/rbtree_size_metadata.click
```

```text
fold requires the instance body facts for the proposed fields
fact 6 of 9 of arm `Node` is not established
tactic@82:
  let structure = fold(rb_at(p), { model: RbTree::Node(identity, parent, color, ...) }, ...
required body fact: <pointer A> == parent
```

The insert loop sidecars fail at loop entry:

```text
loop 0 invariant 1 entry, owing `((uint64)...) == ((uint64)...) implies parent == parent`
```

Affected: `rbtree_size_metadata`, `rbtree_size_rotate_set_parents`, and the
13 loop sidecars `rbtree_size_insert_{black_parent,color_flip,
context_color_flip,context_double_rotation,context_rotation,context_stop,
double_rotation,mirrored_color_flip,mirrored_context_color_flip,
mirrored_context_double_rotation,mirrored_context_rotation,
mirrored_double_rotation,mirrored_rotation,rotation}.click`.
`rbtree_size_change_child.click` fails a different body fact
(`old(*<pointer A>) != old(parent->rb_left)`, tactic@94) and is probably the
same cause, unconfirmed.

Acceptance: the sized resources state the parent relationship as `rb_at`
does (contract adaptation, no C change), every listed sidecar verifies, and
`click audit --keep-going --time-limit 90m examples/rbtree/rbtree-augmented` has no
new failures. Consider moving one fast sidecar such as
`rbtree_size_metadata.click` into the gate so a kernel change like #1245
cannot break this directory unseen.

## Three sidecars after resource-argument view matching

Resource-argument identity now ignores the view a cast selects, so
`compute_size(old, 0)` accepts a held `size_metadata(rb_old)`. The three
sidecars stopped by that refusal now stop later, cause unconfirmed:

- `rbtree_size_rotate.click`, tactic@68: precondition clause 10 of
  `compute_size` (`node->rb.rb_left != (struct rb_node*)(void*)node`), goal
  `old(old[4]) != __click_call_result0`.
- `rbtree_size_propagate_tree.click`, tactic@97:56: `normalize()` leaves
  `rb == rb`, with a cell walk that does not separate a step from an 8-byte
  read.
- `rbtree_size_propagate.click`, tactic@52: `have propagate_remaining(rb,
  stop) == 1` lowers to no path. This one is unchanged by the view rule.
