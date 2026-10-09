# Expanded Adler loop closure still crosses the simple-tactic tail bound

The general unchanged Adler computation verifies and its expanded certificate
rechecks. However, the deterministic `close_invariants` at statement 689 still
crosses the profile's 500 ms simple-tactic tail bound. Expanding smart search
must not hide a slow simple checker or make it traverse unrelated path state.

## Reproduction

Use the locked pinned adler2 selection and the sidecar assembled by
`tests/rust_import/adler2_helpers.rs::compute_proof(GENERAL_COMPUTE)`. The nightly
`charon_adler2_general_compute_tools_recheck_original_contract` regression
constructs this input without changing Rust source. Verify the original first,
expand the computation claim in place, and profile the resulting sidecar.

The checked computation claim is
`__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract`.

Repeated local profiles on 2026-10-09 measured this simple closer at 1.401 s
and 1.134 s with 32,585 deterministic work units; the original source measured
1.317 s and 32,591 units. All runs verified successfully. The location moves
with expansion; identify the statement and tactic rather than a fixed line.
The profile reports `SIMPLE ENGINE BUG` and recommends reducing this checker
path before more smart expansion. These timings are observations, not a timing
assertion for the normal gate.

## Intended regression and acceptance

- Reduce to a C/Rust loop closer that retains the same invariant shape and
  selected memory/iterator facts. Measure preparation, source presentation,
  checked body replay, and retention separately to identify the actual cost.
- Add deterministic scaling over the relevant invariant/certificate input and
  independently over unrelated locals, effect facts, or path state. A simple
  closer may inspect its explicit obligations and state delta, but must not
  repeatedly scan or clone unrelated path-wide state.
- Keep all obligations, guards, ranking checks, snapshot bindings, and exact
  retained-body judgment checks; a mutated member must still fail.
- Recheck the original and expanded unchanged Adler proof and profile the fixed
  closer. Do not raise tactic limits, stack sizes, or profile thresholds to
  suppress this finding.
