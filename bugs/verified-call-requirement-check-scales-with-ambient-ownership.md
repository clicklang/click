# A verified call's requirement check scales with unrelated owned state

Soundness: sound. The defect is cost only: the check reaches the same verdict
it would reach with an indexed lookup, and no claim verifies that should not.

One `step` over a call to the same callee, with the same explicit resource
map, costs about 1,100 work units of requirement checking in a small proof
and about 400,000 in a proof that owns more of the tree. The callee's
requirements and the named operands are the same size in both; the
difference is ambient owned memory the call does not name. The complexity
contract (`docs/internals/verification-efficiency.md`) requires a simple
tactic to cost `O((q + d) polylog N)`, not to compare its requirements
against unrelated owned ranges.

Reproduced on master `765ede18` with a release build:

```sh
CLICK_TIMINGS=1 target/release/click verify \
    examples/rbtree-augmented/rbtree_size_rotate.click 2>&1 |
    grep 'verified call requirement checking sized_rotate'
CLICK_TIMINGS=1 target/release/click verify \
    examples/rbtree-augmented/rbtree_size_rotate_model.click 2>&1 |
    grep 'verified call requirement checking sized_rotate'
```

Both proofs make the call written as

```click
step(sized_rotate(rb_old, rb_new), { source: s, target: t, left: l, right: r });
```

(`rbtree_size_rotate.click:173` in `sized_rotate_has_size_contract`, and
`rbtree_size_rotate_model.click:175` and `:769` in
`sized_rotate_restores_subtree_size_left`/`_right`, where the subtree model
around the rotated nodes is unfolded). `verified call requirement checking
sized_rotate#inline:rbtree_size_rotate.c` is charged:

| proof | requirement checks | units each |
| --- | --- | --- |
| `sized_rotate_has_size_contract` | 4 | about 1,100 |
| `sized_rotate_restores_subtree_size_left`/`_right` | 6 of 8 | 387,836 to 406,813 |

`click profile examples/rbtree-augmented` reports the two model steps as
the only slow simple tactics in the project, 732 ms (417,891 units) and
585 ms (418,023 units), above the 500 ms simple threshold, and classifies
the project as `SIMPLE ENGINE BUG`. The file verifies in about 10 s
release, of which the eight calls' `verification statement: call` are
2.8 million units.

Where the units go, from the same `CLICK_TIMINGS` run of
`rbtree_size_rotate_model.click`: `fact range coverage: shifted base
relation` runs 7,888 times (1.7 million units), `memory range coverage:
explicit separation` 496 times (0.77 million) and `memory range coverage:
fact range` 1,552 times, against 192 shifted-base queries in the small
proof. Roughly a thousand range-coverage queries per call suggests the
call's required ranges are matched against each owned range in turn
(`range_covered_by_fact_range` through `resource_algebra.rs`'s coverage
fallbacks) rather than looked up by base; that diagnosis is from operation
counts, not yet confirmed by a reduction.

This cost is pre-existing: the file has been unchanged since `52553ca0`
(merged in `da10d6e7`, 2026-10-14), and the verifier at `da10d6e7`
takes the same time on it (9.6 s profiled against 9.2 s on `765ede18`).

## Acceptance criteria

- A reduction that keeps the original pattern: a verified call whose
  resource map names a few owned nodes, made while N other owned tree
  nodes are unfolded, with requirement-checking work measured at several
  N.
- Requirement checking for that call is charged work independent of N up
  to indexing factors, pinned by a deterministic scaling regression per
  `docs/internals/verification-efficiency.md`.
- The two `sized_rotate` steps in `rbtree_size_rotate_model.click` fall
  below the 500 ms simple threshold in `click profile`, with no change to
  the example's proofs or C.
