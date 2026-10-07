# Whole-claim expansion misplaces shared tactics in a nested `__rb_insert` match

## Violated invariant

`click expand` must emit a rewrite that verifies (`AGENTS.md`, "Tooling
stability comes first"), and it must agree with `click audit`.

`click expand --claim <label>` rewrites every smart tactic of a claim in one
run. For the claims below the proof it builds does not verify, although
expanding each of the claim's smart sites by location
(`click expand FILE:LINE`) succeeds and verifies.

## Reproduction

A whole-repository audit found 44 claims whose whole-claim expansion failed.
Forty-three have been fixed. The remaining claim verifies, but its whole-claim
expansion fails with "expanded proof did not verify":

```sh
click expand --claim __rb_insert.contract examples/rbtree-insert/rbtree_insert.click
```

### `__rb_insert`

In the `Color::Red` arm of the match that starts at `match c.model` (source
line 782), the written proof has three `have`s, three `step()`s and one more
`have` before a nested `match cu.model`. The expanded proof puts those seven
tactics inside the nested match's arms, so the nested match runs before them
and its `Context::Top` arm's `contradiction` has no fact to use.

The merge that rebuilds a nested match places the shared tactics before it
only when every path through it recorded the same position
(`merge_path_certificates` in `execution_planning/context.rs`). Here the paths
disagree: tracing shows position lists such as `[83, 83, 113, ...]` and
`[16, 16, 37, ...]`, where the odd one out equals the position of a later
match. Why one path's next recorded match is a later one with an equal header
is not yet known.

## Already fixed

Causes found with these reproductions and fixed, with regression tests in
`src/surface/tests/expansion_tests.rs`:

- tactics written after execution inside a match arm were emitted after the
  match, outside the arm's bindings;
- a nested match recorded its position as the length of the whole proof,
  which includes the arms checked before it, instead of its own path's;
- a call step that lends no instance was printed without its empty binder
  map;
- a tactic in a theorem with a type parameter was expanded without fixing the
  parameter at a rigid type;
- a proof `if` after `execute()` in a claim's own proof was left out;
- after `witness` or `intro` opened a claim following execution, a grouped
  proof's expansion left out the closing tactics;
- a user tactic's expansion included the ending its check supplies.
- after a C `if` with one reachable arm, the continuation's first statement
  was entered without recording its entry point, so the expanded branch that
  followed could not name it.
- `sort3.sorted` ended generated execution arms with predicate unfolds after
  their terminal C steps. A syntactic last-tactic restriction refused these
  arms even though their checked entry and join validated the complete C path.
  The expansion now cold rechecks, while missing C steps and false contracts
  remain rejected.
- `chain_countdown.contract` lost the enclosing proof match when a C branch
  rejoined inside its preservation arm. Retaining the parent case metadata
  keeps the resource unfolds inside their constructor scope; the complete
  expanded claim cold rechecks without planning and rejects a false contract.
- all nine counted-population claims from the original reproduction now expand and reverify. Explicit
  C condition steps retain the kernel's exact successor, including the
  selected pending pthread-create outcome and its resource ledger ancestry.
  Recomputing from the old state lost the failed-create authority or produced
  the wrong member exchange. Each original fixture has a whole-claim
  regression, and the smallest cold rechecks without planning and rejects a
  false failed-create count and a contract omitting successful create.

## Effect on the audit

`click audit` expands a wholly selected claim once, with all its sites, and
audits the sites one at a time only when that fails. For the claims above it
therefore takes the slower path and prints a `NOTE` naming the claim; the
claim passes when every site passes alone, and the summary counts the claims
audited that way.

## Acceptance

- Every command above succeeds and its output verifies.
- A regression test covers the expansion of a proof that unfolds members of a
  counted population.
- `click audit` then treats a claim whose sites pass alone but whose
  whole-claim expansion fails as a failure, and the `NOTE` path and its
  summary count are removed.
