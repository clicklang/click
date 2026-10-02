# A function-level `match` arm cannot close by `contradiction` after a `have`

## Violated invariant

`contradiction` refutes the path it stands on wherever on that path it stands. `docs/concepts/loops-and-invariants.md` states this for an arm of a proof `match` inside a loop's `preserve` ("`contradiction` does not have to be an arm's only tactic"), and `mdtests/preserve_arm_contradiction_after_a_have.md` and `mdtests/preserve_arm_contradiction_after_an_unfold.md` are its regressions.

In a proof `match` at the function's own level the same arm is refused. An arm closes by `contradiction` only when that is its sole tactic, which needs the refuted fact and its exact negation to be available with no bridging step. With a bridging `have` in front, every tactic is accepted and the proof is then declined as a whole:

```
the proof script is valid, but the verifier cannot yet certify it for these 2 contract claims
... It reached the supplied tactic sequence, which is not implemented in this execution context.
```

The sole-tactic form is enough when a `requires` or a loop invariant refutes the arm, because contract lowering and loop heads publish the refutation. It is not enough when the refuting fact is established by the proof, which is the case after a loop that leaves by `break`: what rules an arm out is something each exit stated, not an invariant. The only route left is to complete the impossible arm as if it were reachable.

The root cause has not been investigated. Commit `ccf9a340` fixed the same restriction for `preserve` arms in `plan_execution_match`.

## Reproduction

`mdtests/function_match_arm_contradiction_after_a_have.md` is the reduction and pins the refusal (`expect fail`). It has no loop: one `match` on a held instance, one impossible arm closed by three `have`s and a `contradiction`. Replacing that arm with the single tactic `contradiction(x.model == Cell::Missing);` verifies.

The unchanged Linux `rb_next` meets it after its ascent loop (`mdtests/rb_next.md`, "Where it stops").

## Intended regression

Flip `mdtests/function_match_arm_contradiction_after_a_have.md` to `expect pass`. Add the variant whose bridge is an `unfold` rather than a `have`, mirroring the two `preserve` fixtures, and a negative whose `contradiction` names a fact the path does not deny, mirroring `mdtests/preserve_arm_contradiction_needs_a_refuted_fact.md`.

## Acceptance criteria

- A function-level proof `match` arm, with or without a loop earlier in the function, may end in `contradiction` after any prefix of tactics a `preserve` arm accepts.
- A refuted arm owes no contract claim; an arm whose `contradiction` is not justified is still refused by the proposition as written.
- `click audit` passes on the positive fixtures; `scripts/check.sh` passes.
