# rbtree erase mutations exhaust the smart budget instead of refusing

Soundness: incomplete. Each mutated program is still refused; nothing false
is accepted. The refusal is now a work-budget exhaustion at an earlier `have`,
not the prompt diagnostic at the mutated statement.

A proof of a mutated program must fail promptly at the obligation the
mutation breaks, and smart work for one tactic must not grow until it hits the
budget (see [proof-failure triage](../docs/concepts/proof-failure-triage.md)).
Nine nightly mutation tests of the general unlink in
`examples/rbtree/rbtree-erase/rbtree_erase_augmented.click` now stop at
`__rb_erase_augmented.contract` statement 39, source tactic 89, a `have`:

```
verification budget exhausted inside tactic `have` in `__rb_erase_augmented.contract`
exhausted its deterministic smart work budget after 2000001 units (2000000 limit;
statement 39, source tactic 89)
```

Each test, in `tests/examples.rs`, replaces one C statement in
`rb_erase_augmented.c` and expects a named refusal. The nine are:

- `rbtree_erase_successor_requires_root_replacement`
- `rbtree_erase_deep_successor_refuses_a_skipped_splice`
- `rbtree_erase_deep_successor_refuses_a_skipped_right_attachment`
- `rbtree_erase_deep_successor_refuses_a_skipped_right_parent_update`
- `rbtree_erase_deep_black_leaf_requires_right_parent_update`
- `rbtree_erase_deep_black_leaf_requires_the_splice_parent`
- `rbtree_erase_black_successor_requires_the_fixup_parent`
- `rbtree_erase_black_successor_requires_its_old_parent_as_fixup_parent`
- `rbtree_erase_successor_refuses_a_skipped_left_parent_write`

The unmutated nightly example fails at the same tactic in
`example_projects` under `CLICK_NIGHTLY=1`. At a60ca405 it failed later, at
tactic 194, with "match binding `identity` is already in scope", a failure
that has since been fixed on master.

Bisected along master's merges with
`cargo nextest run --run-ignored all --test examples -E 'test(=rbtree_erase_successor_requires_root_replacement)'`.
All nine pass at ece7636d (#1618) and fail at 4ac03c4f, the merge of #1619
("State each comparison of exact observations in one form"). The same merge
changed which theorem `vector_push`'s expansion applies. Before, it applied
`int32_increment_preserves_order`; now it applies
`int32_increment_strictly_increases` and `int32_increment_upper_bound`. As a
result, `surface::tests::expansion_tests::vector_push_pipeline_has_no_outcome_fallbacks`
fails its retained-step check.

## Acceptance criteria

- The nine tests above pass unchanged: each mutation is refused with its
  named diagnostic, and the C and the proof are not changed.
- Tactic 89 of the unmutated example no longer exhausts the budget.
- A `click profile` trace of tactic 89 on one mutated program shows where
  #1619 added the work. The fix removes that growth; it does not raise the
  budget.
- `vector_push_pipeline_has_no_outcome_fallbacks` passes. If the new theorem
  choice is the intended expansion, its expected step is updated, with the
  reason stated.
