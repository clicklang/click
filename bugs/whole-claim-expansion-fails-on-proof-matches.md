# Whole-claim expansion fails on a returning `branch` arm beside resource steps, and on `__rb_insert`

## Violated invariant

`click expand` must emit a rewrite that verifies (`AGENTS.md`, "Tooling
stability comes first"), and it must agree with `click audit`.

`click expand --claim <label>` rewrites every smart tactic of a claim in one
run. For the claims below the proof it builds does not verify, although
expanding each of the claim's smart sites by location
(`click expand FILE:LINE`) succeeds and verifies.

## Reproduction

A whole-repository audit found 44 claims whose whole-claim expansion failed.
Thirty have been fixed. These fourteen remain; each verifies, and each fails
with "expanded proof did not verify":

```sh
click expand --claim chain_has_next.contract mdtests/match_bindings_in_branch_arm.md
click expand --claim chain_countdown.contract mdtests/loop_preserve_branch_tactic.md
click expand --claim tree_contains.contract examples/modeled-binary-tree/modeled_binary_tree.click
click expand --claim increment_twice.contract mdtests/mutex_population_separate_body.md
click expand --claim run.contract mdtests/modeled_pthread_counted_join.md
click expand --claim run.contract mdtests/modeled_pthread_counted_reverse_join.md
click expand --claim run.contract mdtests/modeled_pthread_counted_shared_forward_join.md
click expand --claim run.contract mdtests/modeled_pthread_counted_shared_join.md
click expand --claim run.contract mdtests/modeled_pthread_counted_shared_partial_then_create.md
click expand --claim run.contract mdtests/modeled_pthread_counted_shared_retained.md
click expand --claim run.contract mdtests/modeled_pthread_counted_shared_symbolic.md
click expand --claim run.contract mdtests/modeled_pthread_retire_after_join.md
click expand --claim sort3.sorted mdtests/sort3_sorted.md
click expand --claim __rb_insert.contract examples/rbtree-insert/rbtree_insert.click
```

### A returning `branch` arm beside resource steps (twelve claims)

The first twelve share a shape: a `branch then { ... } else {}` over a C `if`
whose then-arm returns, in a proof that also folds or unfolds a resource. The
expansion writes the `branch` as a proof-level `if` over a snapshot and loses
the then-arm. In `increment_twice`, whose first `branch` arm is

```
have count(contribution(counter)) == 2 by { simp(); }
unfold(contribution(counter));
unfold(contribution(counter));
unfold(state);
step();
simp();
```

the expansion has

```
if at(statement(4).entry, __click_call_result0) != at(statement(4).entry, 0) {
} else {
    step();
    step();
}
step();
if at(statement(8).entry, __click_call_result1) != at(statement(8).entry, 0) {
```

The then-arm is empty, two steps sit in an else-arm the source left empty, and
the second `if` follows the first instead of nesting in its else-arm. The
later failures follow from that: a snapshot named before any path steps there
(`chain_has_next`, `tree_contains`), a population exchange the kernel refuses,
or a `count(...)` read without its authority.

A returning arm alone does not reproduce it. These verify and expand
correctly: a function with one or two early returns over scalars; the same
with a `have` in the arm; the same after a call step. The resource steps, or
the proof `match` around the `branch` in `chain_has_next`, seem to be what
routes the proof through the failing reconstruction.

`sort3.sorted` reports "expanded execution then arm does not end in a checked
C step" and has no `branch`; it may be a separate cause.

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

## Effect on the audit

`click audit` expands a wholly selected claim once, with all its sites, and
audits the sites one at a time only when that fails. For the claims above it
therefore takes the slower path and prints a `NOTE` naming the claim; the
claim passes when every site passes alone, and the summary counts the claims
audited that way.

## Acceptance

- Every command above succeeds and its output verifies.
- A regression test covers a returning `branch` arm in a proof that also
  unfolds a resource.
- `click audit` then treats a claim whose sites pass alone but whose
  whole-claim expansion fails as a failure, and the `NOTE` path and its
  summary count are removed.
