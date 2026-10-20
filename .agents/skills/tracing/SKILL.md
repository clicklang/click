---
name: tracing
description: Repair a failed Click proof from its goal and trace. Use whenever `click verify` reports a proof error, or `auto`, `execute()`, `step()`, or `simp()` does not prove what you expected, before changing the proof, the contract, the C, or the verifier.
---

# Tracing a failed proof

Follow this loop until it ends at one of the outcomes below. Click's
documentation of this procedure, with the trace notation, is the page
"Tracing a failed proof".

## 1. Classify the error

- `syntax error` or `type error`: fix the reported source. This skill does not
  apply.
- `internal error`: the outcome is `unclear-trace`.
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

No `goal:` line, or a goal you cannot read: the outcome is `unclear-trace`.

## 3. Decide whether `G` is true

Check `G` against the contract, the branch facts, and the C semantics. If some
execution the contract admits makes it false, the outcome is `false-goal`.

## 4. Write the argument as a chain

Write why `G` follows from the premises as intermediate facts, each one a
`have` at the program point:

```text
have A by { ... }
have B by { ... }
// G now follows from A and B
```

If you cannot say why `G` holds, the outcome is `unclear-goal`. If you cannot
write one of the intermediate facts in Click, it is `inexpressible-fact`.

## 5. Run, then refine the first failing link

The first link that fails becomes the new `G`; go back to step 2.

A link that a smart tactic such as `auto` does not prove is too big. Split it
(`A` implies `C` implies `D` implies `B`) and run again. Stop splitting only
when a link is one simple tactic: one `apply ... using`, `unfold`, `step()`,
`rewrite`, `normalize()`, or arithmetic certificate.

Before each run, state in one line which link is new and why it holds. A new
tactic, spelling, or position for the same link is not a new attempt. Never
edit `auto`, raise a budget, or change the C to get past a link.

## Outcomes

Stop at exactly one, and say which:

- `success`: the proof verifies. Keep the explicit links `auto` needed.
- `false-goal`: `G` does not hold on some execution the contract admits. Give
  the counterexample.
- `unclear-goal`: you cannot say why `G` holds. Give `G`, the premises, and
  what you tried.
- `inexpressible-fact`: the argument needs an intermediate fact that Click
  cannot write. Report a bug.
- `failing-tactic`: a link that is a single simple tactic, within what that
  tactic is documented to do, is refused. Report a bug. A smart tactic such as
  `auto` that does not prove a link is never `failing-tactic`: the link is too
  big.
- `unclear-trace`: there is no `goal:` line, the goal cannot be read, or the
  refusal is not "`G` was not proved". Report a bug.

`false-goal` and `unclear-goal` usually mean the claim, the contract, or the
argument needs another look, not that Click is wrong.

## What a bug report contains

- The smallest C and Click that still fail, with the original source pattern,
  and the exact command and its output, including the `goal:` line.
- The chain up to the failure, with every earlier link proved.
- The failing link: its goal, the tactic, and the refusal.
- Why the link holds, in one line of mathematics.
- For `failing-tactic`, the documented behavior of that tactic that covers the
  link. For `unclear-trace`, what in the output is missing or misleading.
