# Whole-claim expansion fails on proofs with a proof `match`

## Violated invariant

`click expand` must emit a rewrite that verifies (`AGENTS.md`, "Tooling
stability comes first"), and it must agree with `click audit`.

`click expand --claim <label>` rewrites every smart tactic of a claim in one
run. For a number of claims whose proof holds a proof `match`, the proof it
builds does not verify, although expanding each of the claim's smart sites by
location (`click expand FILE:LINE`) succeeds and verifies.

## Reproduction

Each of these verifies, and each fails with "expanded proof did not verify":

```sh
click expand --claim read_after_step.contract mdtests/proof_match_after_c_step.md
click expand --claim countdown.contract mdtests/loop_decreases_strict_descendant.md
click expand --claim chain_has_next.contract mdtests/match_bindings_in_branch_arm.md
click expand --claim chain_countdown.contract mdtests/loop_preserve_branch_tactic.md
click expand --claim chain_countdown_decided.contract mdtests/loop_preserve_branch_tactic.md
click expand --claim spin.contract mdtests/loop_body_proof_match_ensuring_inside_a_proof_if.md
click expand --claim rb_next.contract mdtests/rb_next.md
click expand --claim rb_prev.contract mdtests/rb_prev.md
click expand --claim __rb_insert.contract examples/rbtree-insert/rbtree_insert.click
```

The reported errors differ, which suggests more than one cause:

| claim | error in the expanded proof |
| --- | --- |
| `read_after_step` | `fold field model: algebraic initializer must denote one symbolic value` |
| `countdown`, `chain_countdown_decided`, `rb_next`, `rb_prev` | `could not lower match scrutinee: expected an algebraic value` |
| `chain_has_next` | `could not lower proof if condition: no state snapshot was recorded for statement(3...` |
| `chain_countdown` | `cannot fold or unfold resource chain: matched field model has no known construct...` |
| `spin` | `fold requires the instance body facts for the proposed fields` |
| `__rb_insert` | `could not lower match scrutinee: algebraic initializer evaluation stopped at a model field of a resource instance this state does not hold` |

For `__rb_insert` the cause is visible in the output: in the `Color::Red` arm
of the match that starts at `match c.model` (source line 782), the written
proof has three `have`s, three `step()`s and one more `have` before a nested
`match cu.model`. The expanded proof's arm starts at `match cu.model`; the
seven tactics before it are gone, so the nested match runs three statements
early.

The list above came from trying whole-claim expansion on 75 passing mdtests
that hold two or more proof `match`es and a `step()`. It is not a survey of
the corpus.

## Effect on the audit

`click audit` expands a wholly selected claim once, with all its sites, and
audits the sites one at a time only when that fails. For the claims above it
therefore takes the slower path and prints a `NOTE` naming the claim; the
claim passes when every site passes alone, and the summary counts the claims
audited that way.

## Acceptance

- Every command above succeeds and its output verifies.
- A regression test expands a claim whose match arm holds tactics before a
  nested proof `match` and checks that those tactics are in the output.
- `click audit` then treats a claim whose sites pass alone but whose
  whole-claim expansion fails as a failure, and the `NOTE` path and its
  summary count are removed.
