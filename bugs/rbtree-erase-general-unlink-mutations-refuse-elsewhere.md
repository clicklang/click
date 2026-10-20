# rbtree general-unlink mutations refuse elsewhere or exhaust the smart budget

Soundness: incomplete. Each mutated program is still refused; nothing false
is accepted. Three refusals are a work-budget exhaustion instead of the
prompt diagnostic at the mutated obligation. The other three name a different
obligation or explanation than their test expects.

A proof of a mutated program must fail promptly at the obligation the
mutation breaks, and smart work for one tactic must not grow until it hits the
budget (see [proof-failure triage](../docs/concepts/proof-failure-triage.md)).
Each test below is a nightly `general_erase_refuses_mutation` test in
`tests/examples.rs`. It replaces one C statement in `rb_erase_augmented.c` and
verifies `examples/rbtree/rbtree-erase/rbtree_erase_augmented.click`. The
unmutated example verifies.

Reproduce one test, in a debug build, with:

```sh
RUST_MIN_STACK=8388608 cargo test --test examples \
  rbtree_erase_child_successor_requires_blackening -- --include-ignored
```

## Budget exhaustion at tactic 338

These three expect
"could not establish `cid->__rb_parent_color == (((uint64)mp) | 1)`":

- `rbtree_erase_child_successor_requires_blackening`
- `rbtree_erase_child_successor_requires_parent_color_write`
- `rbtree_erase_deep_successor_refuses_the_wrong_replacement_parent`

Each fails at the bare `have cid->__rb_parent_color == (address(mp) | 1);`
(line 1191 of the sidecar), which defaults to `simp`:

```
`have` failed for `cid->__rb_parent_color == (address(mp) | 1)`: verification
budget exhausted inside tactic `have` in `__rb_erase_augmented.contract`
exhausted its deterministic smart work budget after 2000001 units (2000000
limit; statement 62, source tactic 338)
```

Under `CLICK_TIMINGS=1`, about 1.68M of those units fall in one
"simp closure: indexed goal equality rewrite" operation, which offers only
seven candidate equalities. No candidate reaches its checked `rewrite` step,
so the work goes into the search before it, most likely
`available_surface_fact`'s spelling lookup for each candidate, which no named
operation measures.

## A different refusal

- `rbtree_erase_left_child_requires_blackening` expects
  "could not establish `el_id->__rb_parent_color == pc`". It now fails at
  tactic 27, "`have` failed for `(pc & 1) == color_bit(Color::Black())`", with
  "`rewrite` requires its equality to be an exact available fact".
- `rbtree_erase_successor_refuses_a_skipped_parent_color_write` expects
  "fact 5 of 9 of arm `Right` is not established". It now reports "fact 5 of
  10". This is the same fold; the arm may have gained a fact since the
  expectation was written.
- `rbtree_erase_successor_requires_left_subtree_link` expects "could not
  establish `mid->rb_left == lid`". It now fails at the same `have`
  ("`have` failed for `mid->rb_left == lid`"), but explains it with
  "`transport using` requires an exact premise".

## Acceptance criteria

- The three tactic-338 tests refuse promptly with their expected diagnostic.
  A `click profile` of one shows where the work went, and the fix removes that
  growth. It does not raise the budget.
- For each of the other three, either the refusal returns to the expected
  obligation and explanation, or the expectation is updated with the reason
  the new diagnostic is the intended one.
- The C and the proof are not changed.
