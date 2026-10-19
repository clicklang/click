---
name: tracing
description: Repair a failed Click proof from its goal and trace. Use whenever `click verify` reports a proof error, or `auto`, `execute()`, `step()`, or `simp()` does not prove what you expected, before changing the proof, the contract, the C, or the verifier.
---

# Tracing a failed proof

Follow this loop. The full procedure, with trace notation, is
`docs/concepts/tracing.md`.

## 1. Classify the error

- `syntax error` or `type error`: fix the reported source. This skill does not
  apply.
- `internal error`: reduce it and stop at outcome 2.
- `proof error`: continue.

## 2. Record the goal

From the ordinary report, write down:

- the goal `G`, from the `goal:` line;
- the program point where `G` is required (a C statement requirement is a goal
  at that statement's pre-state);
- the premises available there.

If the report does not explain the premises, rerun the command under
`To get a trace:` (`click verify --trace-proof PROOF SIDECAR`, optionally with
`--trace-to LINE`). Read its `failed check` section. Ignore `snapshot#N` and
`value#N` legend entries unless the goal depends on telling memories apart.

No `goal:` line, or a goal you cannot read: stop at outcome 2.

## 3. Decide whether `G` is true

Check `G` against the contract, the branch facts, and the C semantics. If some
execution the contract admits makes it false, stop at outcome 6.

## 4. Write the argument as a chain

Write why `G` follows from the premises as intermediate goals, each one a
`have` at the program point:

```text
have A by { ... }
have B by { ... }
// G now follows from A and B
```

Can't say why `G` holds: outcome 3. Can't write an intermediate goal in Click:
outcome 4.

## 5. Run, then refine the first failing link

The first link that fails becomes the new `G`; go back to step 2.

A link that `auto` does not prove is too big. Split it (`A` implies `C`
implies `D` implies `B`) and run again. Stop splitting only when a link is one
simple tactic: one `apply`, `unfold`, `step()`, rewrite, or arithmetic step.

Before each run, state in one line which link is new and why it holds. A new
tactic, spelling, or position for the same link is not a new attempt. Never
edit `auto`, raise a budget, or change the C to get past a link.

## Outcomes

Stop at exactly one, and report which:

1. **Proved.** Keep the explicit links `auto` needed.
2. **Diagnostic defect.** No `goal:`, an unreadable goal, or a refusal that is
   not "`G` was not proved". Reduce it to a small sidecar.
3. **No argument.** You cannot say why `G` holds. Report `G`, the premises,
   and what you tried.
4. **Inexpressible intermediate goal.** Click cannot write a fact the argument
   needs. Report it mathematically, with the reduced sidecar.
5. **Refused simple step.** A link that is a single named simple tactic is
   refused. Report the link, the tactic, and the refusal. "`auto` did not
   prove it" is never outcome 5.
6. **False goal.** Give the counterexample. Propose the contract or C change;
   do not weaken a claim yourself.

For outcomes 2, 4, and 5, keep the reproduction and ask the user before
changing the verifier, unless it is a reproduced bug in existing behavior.
