---
name: tracing
description: Repair a failed Click proof from its goal and trace. Use whenever `click verify` reports a proof error, or `auto`, `execute()`, `step()`, or `simp()` does not prove what you expected, before changing the proof, the contract, the C, or the verifier.
---

# Tracing a failed proof

Follow this loop until it ends at one of the outcomes below. `click docs
tracing` prints Click's documentation of this procedure, with the trace
notation, and `click docs NAME` prints any tactic's forms, class, and
documented behavior.

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
`--trace-to LINE`). Read its `failed check` section.

A goal about memory (any `transport`, frame, or `read<...>(snapshot#N, ...)`
goal) depends on its `snapshot#N` and `value#N` labels: write down the legend
line that defines each label the goal uses. Two spellings of one C address
(`p` and `g + 16 bytes`, or a read at entry and a read in the loop) are often
the whole story. Otherwise ignore the legend.

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

A refusal ends with `refused by:`, naming the tactic and its class, when
Click can tell. A link that a smart tactic such as `auto` does not prove is too
big. Split it (`A` implies `C` implies `D` implies `B`) and run again. Stop splitting only
when a link is one simple tactic: one `apply ... using`, `unfold`, `step()`,
`rewrite`, `normalize()`, or arithmetic certificate.

Before each run, state in one line which link is new and why it holds. A new
tactic, spelling, or position for the same link is not a new attempt. Never
edit `auto`, raise a budget, or change the C to get past a link.

## 6. Shrink a refused simple link

Before reporting a refused simple link, make the link itself as small as it
will go, not only the program around it:

- Drop each `using` premise, alias, and earlier `have` it does not need, one
  at a time, keeping the refusal.
- Write it with the most direct spelling: the C local the statement uses
  rather than a spec alias for it.
- Find the nearest link that passes, such as the same transport of another
  field across the same store, and say what differs between the two (the
  field's type and width, its offset, the address spelling).

Then compare the refusal with the one-line argument and name the step Click
did not take: which two addresses it did not identify, which read it did not
carry, which fact it did not read.

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
  tactic is documented to do (the **Accepts** list in `click docs NAME`), is
  refused, still in its smallest form after step 6. Report a bug. A smart tactic such as `auto` that does not prove a
  link is never `failing-tactic`: the link is too big.
- `unclear-trace`: there is no `goal:` line, the goal cannot be read, or the
  refusal is not "`G` was not proved". Report a bug.

`false-goal` and `unclear-goal` usually mean the claim, the contract, or the
argument needs another look, not that Click is wrong.

## What a bug report contains

- The smallest C and Click that still fail, with the original source pattern,
  and the exact command and its output, including the `goal:` line.
- The chain up to the failure, with every earlier link proved.
- The failing link in its smallest form (step 6): its goal, the tactic, and
  the refusal, with the legend lines for every label the goal uses.
- The nearest passing link and what differs from it.
- Why the link holds, in one line of mathematics, and the step of that
  argument Click did not take.
- For `failing-tactic`, the item of that tactic's **Accepts** list that
  covers the link. For `unclear-trace`, what in the output is missing or
  misleading.
