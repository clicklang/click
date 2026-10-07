# Whole-claim expansion fails on a `branch` inside a proof `match`, and on `__rb_insert`

## Violated invariant

`click expand` must emit a rewrite that verifies (`AGENTS.md`, "Tooling
stability comes first"), and it must agree with `click audit`.

`click expand --claim <label>` rewrites every smart tactic of a claim in one
run. For the claims below the proof it builds does not verify, although
expanding each of the claim's smart sites by location
(`click expand FILE:LINE`) succeeds and verifies.

## Reproduction

Each of these verifies, and each fails with "expanded proof did not verify":

```sh
click expand --claim chain_has_next.contract mdtests/match_bindings_in_branch_arm.md
click expand --claim chain_countdown.contract mdtests/loop_preserve_branch_tactic.md
click expand --claim __rb_insert.contract examples/rbtree-insert/rbtree_insert.click
```

### A `branch` inside a match arm

`chain_has_next` has, inside one arm of a proof `match`, two `branch then { ...
} else {}` tactics over C `if`s whose then-arms return early. The expansion
writes each as a proof-level `if` over a snapshot:

```
if at(statement(0).entry, p) == at(statement(0).entry, 0) {
} else {
    step();
    step();
}
if at(statement(3).entry, load_int32_pointer(p)) == at(statement(3).entry, 0) {
```

The first `if` has lost its then-arm's steps, and the second names
`statement(3).entry` before any path has stepped there, which is the reported
error: "could not lower proof `if` condition: no state snapshot was recorded
for `statement(3).entry`".

`chain_countdown` is a `branch` in a loop's `preserve` proof and fails with
"cannot fold or unfold resource `chain`: matched field `model` has no known
constructor".

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

Two causes found with these reproductions are fixed, with regression tests in
`src/surface/tests/expansion_tests.rs`:

- tactics written after execution inside a match arm were emitted after the
  match, outside the arm's bindings;
- a nested match recorded its position as the length of the whole proof,
  which includes the arms checked before it, instead of its own path's.

## Effect on the audit

`click audit` expands a wholly selected claim once, with all its sites, and
audits the sites one at a time only when that fails. For the claims above it
therefore takes the slower path and prints a `NOTE` naming the claim; the
claim passes when every site passes alone, and the summary counts the claims
audited that way.

## Acceptance

- Every command above succeeds and its output verifies.
- A regression test covers a `branch` with an early-returning arm inside a
  proof `match` arm.
- `click audit` then treats a claim whose sites pass alone but whose
  whole-claim expansion fails as a failure, and the `NOTE` path and its
  summary count are removed.
