# Integer count `auto()` certificate rewrites with an equality the goal no longer contains

Soundness: incomplete. A proof that verifies is rejected only when its smart
`auto()` is expanded and re-checked; nothing false is accepted.

`auto()` must expand to explicit steps that the simple checker accepts.
Under `arithmetic "integer";`, `have count(pool_slot(pool)) == 0 by auto();`
verifies, but its expanded certificate starts with a `rewrite` by the ledger
fact
`to_integer(old(pool[1])) == to_integer(old(*pool)) + to_integer(old(count(pool_slot(pool))))`
while the goal at that point is the word comparison
`old(count(pool_slot(pool))) - old(pool[1]) == 0`, and the re-check refuses it:
"`rewrite` equality does not occur in the current goal". The smart search and
the simple checker disagree on the goal's form.

Bisected: passes at ece7636d (#1618) and fails at 4ac03c4f, the merge of #1619
("State each comparison of exact observations in one form"), which changed
how integer comparisons are stated (`arithmetic_special.rs`,
`integer_arithmetic.rs`, `equality_rewrite.rs`).

## Reproduction

`mdtests/an_integer_count_equality_retires_its_authority.md` still passes
`click verify`, which the gate runs, but `click audit` on it fails:

```
pool_destroy.contract tactic 2: `have` failed for `to_integer(count(pool_slot(pool))) == 0`:
  `pool_destroy.contract` proof step tactic 2 > have body tactic 1:
  `rewrite` equality does not occur in the current goal
```

`click expand <file>:19:5` shows the same refusal with the equality and goal
above. The original pattern also fails audit in
`examples/bounded-pool/bounded_pool.click` (`pool_destroy.contract`, 2
sites). Both programs should be kept unchanged as the regression.

## Acceptance criteria

- `click audit` passes `pool_destroy.contract` in
  `examples/bounded-pool/bounded_pool.click` and in
  `mdtests/an_integer_count_equality_retires_its_authority.md`, with the
  proofs unchanged.
- The expansion's steps are stated in the goal form the simple checker
  sees after #1619; the checker is not loosened to accept a rewrite that is
  not in its goal.
- A gate-sized regression expands and re-verifies this `have` (for example
  the mdtest's expansion check), so the disagreement cannot come back
  between nightly audits.
