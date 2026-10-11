# `rbtree-insert` fails at a branch join after checked-join read preservation

## Violated invariant

A proof that verified before a change that only adds facts at branch joins
must still verify. Commit `9ed99f3b` (clicklang/click#679, "Preserve
uncached reads across checked branch joins") makes the nightly example
`examples/rbtree-insert` fail; its parent, `e3884ccc`, verifies it
(23 selected proofs).

## Reproduction

```sh
cargo build --bin click
target/debug/click verify examples/rbtree-insert
```

On `9ed99f3b` this reports:

```text
proof error:
  `branch ensuring` arms produced different abstract successor states
  they differ in the memory (incoming branch memories)

tactic@1197:
  have uu.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
```

The failing join is the `match` on `xsib` around
`examples/rbtree-insert/rbtree_insert.click:1185`: both arms unfold and
refold the sibling, and the join now compares the arms' incoming branch
memories, which differ, where before it did not.

`rbtree-insert` is in the `NIGHTLY` list of `tests/examples.rs`, so the gate
does not run it and the regression merged green.

## Acceptance criteria

- `click verify examples/rbtree-insert` verifies on the fixed tree with the
  sidecar unchanged.
- A gate-sized regression reproduces the shape: two arms of a branch whose
  joined successor states differ only in how each arm reached the same
  memory (here, unfold and refold of one instance), joined after the
  `BranchJoin` derivation records incoming memories.
