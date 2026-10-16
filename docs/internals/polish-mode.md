# Polish mode

Polish mode is a development workflow for improving Click through real
verification work and recorded usability friction. It is a future pass to
undertake once the basic functionality has settled, not a command, runtime
mode, or change to verification semantics. This page records the workflow;
it does not start a polish pass or schedule one.

The goal is to make the next verification task easier for an AI proof author.
A successful proof is useful evidence, but so is an ordinary rejected step
whose explanation makes the correction obvious. Measure progress by whether
the author can understand and act on the tools' output without inspecting
Click's implementation or guessing through repeated variations.

## Run a polish pass

1. Choose a small set of real verification tasks using the supported language
   surface. Include an unfamiliar example or an extension to an existing proof,
   rather than only rerunning established proofs. Record the revision, task,
   starting files, and intended property.
2. Work as a proof author using the documented tools. Keep the existing program
   and intended claim as the boundary; follow the
   [proof-failure triage](../concepts/proof-failure-triage.md) policy rather
   than rewriting correct C or weakening a claim to avoid friction.
3. Make a short note whenever progress requires guesswork, source inspection,
   repeated tactic variations, awkward bookkeeping, or waiting without useful
   feedback. Note friction during successful work too: a passing proof can
   still be difficult to discover, express, or maintain.
4. On a failure, first read the ordinary report, then use a focused trace when
   needed. Follow the existing three-strikes rule. Record separately what the
   ordinary output explains, what tracing adds, and what remains unexplained.
5. At a coherent checkpoint, review the notes and choose a small improvement
   supported by the evidence. Reproduce it, classify it, make the appropriate
   change, and retry the original task. Keep unresolved notes with links to
   any resulting bug reports or approved follow-up work.

Promptly investigate crashes, invalid expansions, inconsistent tool results,
and unexpected slowness under the existing tooling-defect policy. A polish
pass is not a reason to defer a known reliability defect until the review.

## What to look for

For every failed check, ask:

- What exactly must be established, and at which source or proof location?
- What relevant facts, permissions, and snapshot evidence are available?
- Where did matching, reasoning, or execution stop? Can the output distinguish
  a missing premise, a bounded search miss, an unsupported operation, and an
  internal failure?
- Does the ordinary error support the next action? If a trace is needed, does
  it supply the missing detail without burying it in unrelated output?

Also watch the surrounding workflow: finding the right command or tactic,
selecting a proof, discovering supported syntax, expressing routine reasoning,
interpreting progress and timing, and returning to a task after interruption.
Record a concrete obstacle rather than a general preference for more output or
more automation. Too much diagnostic output can be an obstacle too.

## Keep lightweight notes

Keep notes beside the task's reviewable artifacts, for example in a task-local
Markdown log attached to its PR. Preserve the original example and output;
link a smaller reproduction when one is available. Do not require a polished
bug report before recording an observation.

Use this template for each distinct obstacle:

```text
Task and revision:
Input files, selected claim, and command:
Intended next step / expected information:
Observed output (or link to the saved output):
What the ordinary report explains:
What the focused trace adds:
What remained unclear / extra work required:
Classification and proposed improvement:
Disposition (open, corrected proof, bug link, PR link, or deferred):
Retry result on the original task:
```

Separate observed evidence from hypotheses about the cause. Record time or
attempt counts when they help explain the cost; do not create quotas for the
number of findings or force every ordinary proof mistake into a tool change.

## Turn observations into improvements

Use the existing triage categories. Correct a mistaken proof or specification
when the output already explains it. Improve documentation when supported
behavior is hard to discover. Propose a diagnostic or workflow change when
relevant information is missing or difficult to use. File reproduced verifier
or tooling defects in `bugs/` under the
[contribution workflow](contributing.md); notes alone are not confirmed bugs.

Tooling design changes still require the user's approval, and new roadmap
entries require an explicit request. Approval to conduct a polish pass does
not authorize arbitrary new syntax or broader feature work. Prefer a focused
improvement with a preserved example over a speculative redesign.

For each improvement, retry the original task and check whether the obstacle
actually disappeared. For a failure explanation, this means an author can
identify the obligation, relevant evidence, and stopping point from the report
and trace. Add a regression appropriate to the change and record any remaining
friction. A pass ends with a short account of tasks attempted, improvements
delivered, and unresolved observations so the next pass can resume from evidence.
