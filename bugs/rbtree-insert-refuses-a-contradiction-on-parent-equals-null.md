# `rbtree-insert` refuses a `contradiction` on `parent == 0`

The nightly example `examples/rbtree/rbtree-insert` fails on `master`
(`d421e24fd`). It is in `NIGHTLY` in `tests/examples.rs`, so the gate does not
run it.

## Reproduction

```sh
cargo build --bin click
target/debug/click verify examples/rbtree/rbtree-insert
```

```text
proof error:
  `contradiction(parent == 0)` requires an exact fact and its exact negation or opposite condition polarity
  `parent == 0` is available, but neither `not (parent == 0)` nor its opposite comparison is
```

The nightly examples `rbtree-erase` and `rbtree-augmented`, which import the
same model, also report `fold` refusals at this point
(`((load_uint64(p) & ~3) as (struct rb_node *)) == parent` and
`node->rb_right != node` not established). Those two have not been checked on
`master` separately.

## Violated invariant

A checked example proof keeps verifying. The proof at `rbtree_insert.click`
tactic 532 cites a fact that the current state no longer holds in the exact
polarity it names: either an earlier change dropped the `parent != 0` fact the
proof relied on, or the proof needs updating to state it.

## Acceptance criteria

- `click verify examples/rbtree/rbtree-insert` passes, with the C unchanged.
- The nightly example run passes for `rbtree-insert`, and the cause of the
  `rbtree-erase` and `rbtree-augmented` refusals is either fixed in the same
  change or filed separately.
