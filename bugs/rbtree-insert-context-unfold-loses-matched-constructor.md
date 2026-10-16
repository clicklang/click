# rbtree_insert context unfold loses the matched constructor

Priority: P2.

Soundness: not soundness. The verifier refuses a proof that it accepted before,
and the nightly `rbtree-insert` example fails. No false claim is accepted.

The violated invariant is that inside a `match c.model { Context::Left(...) => ... }`
arm, `unfold(c)` on an owned `ctx_at` resource selects the `Left` constructor.
That constructor names `sibling` and `up` children. The match arm establishes
`c.model == Context::Left(cid, cgp, ccolor, csib, cup)` as a fact.

## Reproduction

On `master` at `4be82873`, run
`click verify examples/rbtree-insert/rbtree_insert.click`:

```text
proof error:
  `sibling` is not a named child of `ctx_at` here

tactic@531:
  let { sibling: cs, up: cu } = unfold(c);
```

The unfold is in `__rb_insert`'s first loop. It is the `parent == 0` case of the
`Context::Left` arm under `match c.model`, just before `contradiction(parent == 0)`.

The example verifies at `5ebb6065` (23 proofs) and fails from `b11f1ec3` on, the
merge of clicklang/click#1157 ("Use shared model constructors for owned rbtree
contexts"). That change selects a resource's model constructor through shared
equality classes (`src/kernel/assumptions.rs`, `src/kernel/equality_graph`).
In this arm, the selection no longer finds the `Left` constructor that the match
fact names.

The example is listed in `NIGHTLY` in `tests/examples.rs`, so the PR gate does
not run it. The nightly run fails.

## Acceptance criteria

- `click verify examples/rbtree-insert/rbtree_insert.click` verifies again, with
  the C source and proof unchanged.
- A gate-sized regression covers `unfold` of a `ctx_at`-shaped resource inside a
  `match` arm on its model. That regression is refused at `b11f1ec3` and
  accepted after the fix. The two resource-unfold regressions that clicklang/click#1157
  added keep passing.
