# rbtree_size_rotate_model's fold lacks the complete instance body

Soundness: incomplete. An existing checked proof is refused; nothing false
is accepted.

`examples/rbtree/rbtree-augmented/rbtree_size_rotate_model.click` verified before
#1245 (`2cee79c02`, pointer designation) and is refused on master
`a69f1cff2`:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-augmented/rbtree_size_rotate_model.click
```

```text
fold requires ownership of the complete instance body
tactic@201:
  let demoted_checked = fold(sized_at(rb_old), { model: SizedTree::Node(identity, parent, color, 1, left_model, right_model) }, { metadata: metadata, left: left, ...
```

Not investigated; it may share a cause with
`rbtree-augmented-sized-resources-lack-the-parent-pointer-fact.md` or
`resource-argument-equality-compares-pointer-views.md`. Trace with
`click verify --trace-proof sized_rotate_restores_subtree_size_left
examples/rbtree/rbtree-augmented/rbtree_size_rotate_model.click`.

Acceptance: the cause is identified, reduced to a gate regression keeping
the fold pattern (or folded into one of the bugs above), and the sidecar
verifies.
