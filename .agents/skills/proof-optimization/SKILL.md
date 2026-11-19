---
name: proof-optimization
description: Diagnose a slow Click proof, reduce avoidable work, and explain the remaining cost or isolate a verifier defect. Use when verification is unexpectedly slow or when optimizing a proof that already verifies.
---

# Optimize a Click proof

Use [Profiling](../../../docs/concepts/profiling.md) and the
[`click profile` reference](../../../docs/reference/cli/profile.md) to locate
the cost. Keep the program, contract, and verification scope fixed when
comparing a proof before and after a change.

## 1. Establish a baseline

Run `click verify TARGET` and `click profile TARGET` on the slow sidecar,
project, or Markdown fixture. Record the Click revision, build profile,
target, limits, elapsed verification time, and reported work. Compare times
on the same machine with comparable cache state. Prefer deterministic work
to interpret small or noisy timing changes.

For a prompt proof failure, use [proof-repair](../proof-repair/SKILL.md).
Profile a timeout or unexpectedly slow incomplete run to locate where it
stopped. Use a successful run as the baseline for expansion.

For an example, check the
[proof size and speed targets](../../../docs/internals/verification-efficiency.md#proof-size-and-speed-targets).
About 20 proof lines per C line is the size target. About 300 proof lines per
second is acceptable and 700 or more is good. Use comparable optimized
measurements for throughput. A proof can run at a good rate and still take a
long time because of its size. These figures guide triage. The class-specific
thresholds in the profiler flag individual sites. The two measures answer
different questions.

## 2. Follow the profile

- **SMART.** For a completed expensive tactic in a verified proof, try the
  report's [`click expand` command](../../../docs/reference/cli/expand.md) at
  that site or its enclosing claim. Verify and profile the exact rewritten
  source with the original limits. If the emitted proof is large, look for a
  shorter checked argument or explicitly supply the facts the search needed.
  A prompt bounded search miss uses the proof-repair workflow.
- **CONTROL.** Inspect the nested tactic rows and follow their classes.
- **SIMPLE.** A reproducibly slow checked operation above its reporting
  threshold is a verifier performance defect to reduce. Inspect its named
  operations and measure how their work grows with selected inputs and with
  unrelated context. Use the
  [verification efficiency contract](../../../docs/internals/verification-efficiency.md#complexity-contract)
  to judge whether the operation reads work it should avoid.
- **Work outside tactics.** Inspect the phase or operation the report
  attributes it to. Check whether loading, certification, or another phase
  dominates before changing the proof.

If expansion of a successful tactic emits a proof that fails verification,
or cannot render a supported successful certificate, preserve that
reproduction as a tooling defect. If the expanded proof verifies but a simple
operation remains slow, reduce that operation. Keep the original proof and
profile when reducing a defect, and keep the verification budgets fixed.

## 3. Report the outcome

- **Sped up.** Give the checked change and comparable before-and-after
  measurements. Include proof size when expansion materially changes it.
- **Cost explained.** Give the measured work and identify the proof obligations,
  paths, or data that account for it. Include the throughput when it explains
  why a long proof takes that much time. Use measurements at different sizes
  when making a scaling claim.
- **Click defect.** Give the smallest reproduction you found, the profile and
  relevant work counts, and the specific operation or expansion failure.
  Follow [verifier-design](../verifier-design/SKILL.md) for changes to the
  verifier, and use a deterministic scaling regression for a performance
  fix. Follow the repository's [reporting workflow](../../../docs/internals/contributing.md)
  for any issue.
