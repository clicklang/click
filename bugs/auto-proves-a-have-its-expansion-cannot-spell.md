# `auto` proves a `have` its expansion cannot spell

Soundness: not soundness. The proof `auto` finds is kernel-checked, and the
expansion refuses to emit text it cannot spell; only `click expand` fails.

`have P by auto;` can verify while `click expand` of the same site cannot
write the proof out. A smart tactic's success must come with an expansion
that verifies, so this breaks the expand contract: the certificate cites a
value the kernel introduced that has no source spelling.

Reproduced on master `cb2bf3c6`. In
`examples/rbtree-insert/rbtree_insert.click`, replace the proof of

```click
have rb_inorder(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by { ... }
```

(line 711 on that commit, inside `__rb_insert`'s proof) with `by auto;`.

- `click verify rbtree_insert.click:711:41` reports `1 selected proof
  verified`.
- `click expand rbtree_insert.click:711:234` fails with `the expansion needs
  a name for a value the kernel introduced, which has no surface spelling`.

The hand-written proof rewrites by
`RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(...)` and
then by the earlier `rb_inorder(plug(Context::Top, rb_recolor(...)))`
equality; `auto`'s equality search finds a route through a kernel value
instead.

Intended regression: a small mdtest with a recoloured node in a top-level
context whose `rb_inorder` equality `auto` proves, expecting `click expand`
of the site to produce text that verifies. Keep the rbtree-insert edit above
as the original-pattern case.

Acceptance:

- `auto` on this site either proves it with steps the expansion can spell,
  or does not count a route whose certificate cites an unspellable value as
  a success.
- `click expand` of the site writes a proof that `click verify` accepts.
