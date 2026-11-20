---
name: benchmarking
description: Compare Click verifier runtime and deterministic work before and after an engine change. Use when measuring a performance candidate, interpreting noisy timings, or checking whether a verifier speedup generalizes.
---

# Benchmark Click verification

Use [the benchmark harness](../../../docs/internals/testing.md#comparing-verifier-performance)
when answering whether a change makes verification faster. For a slow proof
whose expensive work is unknown, start with
[proof-optimization](../proof-optimization/SKILL.md).

1. Choose a verifying reproduction and at least one workload outside the
   changed path. Run from a common workload checkout so the source, sidecars,
   captures, and verification scope are identical. Use the same Rust
   toolchain and optimized build profile for both executables. Prefer two
   modes of one binary when a runtime switch is already available.
2. Run `scripts/benchmark-verify.py --baseline /path/to/base/click
   --candidate /path/to/new/click` with the selected targets. Omit
   `--candidate` and specify `--candidate-env NAME=VALUE` for a runtime
   switch. Let the harness warm both variants and alternate their order.
   Use the same machine and avoid concurrent builds or benchmarks.
3. Compare the paired timings and inspect each workload's range. Use the
   separate work log to explain consistent movement. Completed tactic work
   excludes driver and verifier work outside tactics. For a change there,
   use the relevant named operation or a deterministic scaling regression.
   Keep the logs, revisions, build profile, and selected targets so another
   run can reproduce the comparison.
4. Report both timings and the work measure. Call the timing result
   inconclusive when the pairs disagree or the difference is comparable to
   ordinary variation. A proof failure or a different selected scope
   invalidates a speed comparison. Keep wall-clock comparisons out of the
   PR gate and use deterministic scaling tests to enforce work bounds.
