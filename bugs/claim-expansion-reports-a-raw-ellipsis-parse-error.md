# Claim expansion reports a raw `…` parse error

Soundness: not soundness. Only the diagnostic is wrong; no verdict changes.

When an expansion would need a name for a value that has no source spelling,
`click expand` of the single site says so: `the expansion needs a name for a
value the kernel introduced, which has no surface spelling`. Expanding the
whole claim with `--claim` instead renders the value with the diagnostic
placeholder `…` and reports the resulting parse error, which names neither
the site nor the missing name. `UNSPELLABLE_POINTER_FORMS` in
`src/surface/expansion.rs` exists to turn exactly this case into the named
error, so the claim path bypasses it.

Reproduced on master `cb2bf3c6` with the same edit as
[auto-proves-a-have-its-expansion-cannot-spell.md](auto-proves-a-have-its-expansion-cannot-spell.md):
replace the proof of the `rb_inorder(plug(Context::Top, RbTree::Node(nid, 0,
Color::Black, nleft, nright))) == ...` `have` at line 711 of
`examples/rbtree-insert/rbtree_insert.click` with `by auto;`.

- `click expand rbtree_insert.click:711:234` reports the named error above.
- `click expand --claim __rb_insert.contract rbtree_insert.click` reports
  `rbtree-insert/rbtree_insert.click:735: unexpected character `…``
  (`error kind: syntax error`).

Intended regression: the small mdtest for the companion bug, expanded with
`--claim`, expecting the same named diagnostic as the site expansion.

Acceptance:

- Whole-claim expansion that meets an unspellable value reports the same
  named diagnostic as site expansion, naming the site.
- No expansion path reports a parse error caused by diagnostic-only
  placeholder text.
