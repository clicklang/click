---
name: tracing
description: Repair a failed Click proof from its goal and trace. Use whenever `click verify` reports a proof error, or `auto`, `execute()`, `step()`, or `simp()` does not prove what you expected, before changing the proof, the contract, the C, or the verifier.
---

# Tracing a failed proof

Follow this loop until it ends at one of the outcomes below. `click docs
tracing` prints Click's documentation of this procedure, with the trace
notation, and `click docs NAME` prints any tactic's forms, class, and
documented behavior.

## Crashes and hangs

Two failures are bugs whatever the proof says, and end this loop at once:

- `crash`: Click exits without a report: a panic, an abort, a stack
  overflow, or the process being killed.
- `hang`: Click runs for a long time without returning. Click bounds its own
  work and stops with a limit error, so a run that does not finish in
  minutes, with no report, is a hang. Stop it and note how long it ran.

Do not change the proof, raise a limit, or retry to get past either one.
Report it (below), labelled `crash` or `hang`, with the exact command, the
`click --version` output, the complete output, and the files needed to rerun
it; shrink them if you can, but a report need not wait for that.

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
Click can tell. `refused by: nothing` means the proof ended with that goal
still open: no tactic failed, and the next link is missing. A link that a smart tactic such as `auto` does not prove is too
big. Split it (`A` implies `C` implies `D` implies `B`) and run again. Stop splitting only
when a link is one simple tactic: one `apply ... using`, `unfold`, `step()`,
`rewrite`, `normalize()`, or arithmetic certificate.

To split a link a smart tactic proved part of, read its trace. A step marked
``(from `execute`)``, ``(from `auto`)`` or ``(from `implicit auto`)`` is one
that tactic took, and a `chosen:` line is the written form of an argument its
search chose. Writing those steps and forms out turns the searched part of
the link into simple tactics, so the remaining gap is the link to split.

A refusal that says "this is a search miss" came from an elided form, such
as `apply(t(x))` or a bare `transport(P, Q)`, whose search for an argument
found nothing. Write the argument: state the missing fact with `have` first,
or write the `using` form it names. Only the written form's refusal can be
`failing-tactic`.

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
  cannot write. Report a bug (below).
- `failing-tactic`: a link that is a single simple tactic, within what that
  tactic is documented to do (the **Accepts** list in `click docs NAME`), is
  refused, still in its smallest form after step 6. Report a bug (below). A smart tactic such as `auto` that does not prove a
  link is never `failing-tactic`: the link is too big. A search miss is
  never `failing-tactic` either: write the argument and run again.
- `unclear-trace`: there is no `goal:` line, the goal cannot be read, or the
  refusal is not "`G` was not proved". Report a bug (below).

`false-goal` and `unclear-goal` usually mean the claim, the contract, or the
argument needs another look, not that Click is wrong.

## Reporting a bug

The three bug outcomes, a crash, and a hang are defects in Click. To report
one:

1. Get the user's approval before reporting it.
2. Open an issue at https://github.com/clicklang/click/issues.
3. Give the report below, enough for someone else to reproduce it.
4. Label the issue with its outcome: `tracing: inexpressible-fact`,
   `tracing: failing-tactic`, `tracing: unclear-trace`, `crash`, or `hang`.
   Start the title with it in brackets too (`[failing-tactic] ...`,
   `[hang] ...`), so it shows even where you cannot set labels.

## What a bug report contains

A crash or hang report contains what its section above lists. A report of
one of the three outcomes contains:

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
