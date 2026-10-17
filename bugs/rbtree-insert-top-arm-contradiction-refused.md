# rbtree_insert's Top-arm contradiction is refused

Soundness: incomplete. An existing checked proof is refused; nothing false
is accepted.

`examples/rbtree-insert/rbtree_insert.click` verified before #1245
(`2cee79c02`, pointer designation) and is refused on master `a69f1cff2`;
the `rbtree-insert` sources did not change in between.

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree-insert/rbtree_insert.click
```

```text
in match arm `Context::Top`
constructor-arm `contradiction` requires an exact fact and its negation in that arm; refused `contradiction(c.model == Context::Top())`
tactic@642:
  contradiction(c.model == Context::Top);
```

Suspected, not confirmed: #1245 changed `predicate_fact_refutes_constructor`
to compare only indexed scalar evidence, and changed `rb_at`/`ctx_at` in
`examples/rbtree-model`. A first reduction attempt also failed before #1245,
so no valid small reproduction exists yet; producing one that keeps the
original `match c.model { Context::Top => contradiction(...) }` pattern is
part of the fix.

Acceptance: a gate reduction that fails on master and passes with the fix,
`rbtree_insert.click` verifies, and a contradiction without a refuting fact
in the arm is still refused.
