# Zlib full-stream expansion loses a pointer invariant proof

Soundness: not soundness. The original full-stream contract and its helper
bodies verified against the locked, unchanged C source, but rechecking its
expanded certificate failed. No false acceptance is known.

The failure did not reproduce on upstream `471284951`: the named full-stream
test passes, including all helper bodies, the complete
expanded certificate, and all six mutation controls. A separately captured
certificate also passes a cold CLI check. Its corresponding pointer step uses
explicit rewrites and `assumption()`, rather than the failing
`normalize() using` step reported below. These observations do not identify a
fix or establish that every generated certificate rechecks; retain this report
until the failing selection is understood. Capture the actual failed expansion on
the next reproduction, rather than inspecting a newly generated certificate.

A fresh run on `776dedeac` stopped earlier in the original proof: its full-batch
cursor join could not compose two full pointer-value equalities through their
displacements. Repairing that substitution restores the original body proof.
Selected runs also pass the complete expanded certificate and all six mutation
controls, but a fresh run after integration with `a93a36d75` again fails at the
historical expanded `normalize using` step below. The reduced C-argument
regression is
`mdtests/pointer_value_equalities_compose_through_displaced_arguments.md`, with
symbolic snapshot-base and selected-bound controls in the kernel rewrite tests.
The failing certificate selection remains unidentified, so keep this report
until that selection is understood.

The incremental C zlib test also passes on this revision, including its
expanded certificate, every helper body, and all five mutation controls:
`pinned_zlib_incremental_c_matches_checked_shared_specification_offline`.

The October 16 nightly initially stopped earlier on an unavailable historical
nonnegativity premise. After proving unsigned `sum2` nonnegativity directly
with the existing `uint64_to_integer_bounds` theorem, this existing test
reproduces a later expansion defect:

```sh
cargo nextest run --profile nightly --test compiler_import --run-ignored only \
  -E 'test(=pinned_zlib_full_stream_matches_checked_shared_specification_offline)'
```

`tests/compiler_import.rs` verifies `design/charon-trial/zlib/full-stream.click`
and every inlined helper body, checks all eight path-specific result and byte
preservation contracts and their import identities, expands the complete
`adler32_z.contract`, then verifies that expanded source with the same prepared
imports. The original verification succeeds; the expanded-source check fails:

```text
`adler32_z.contract` tactic 14 (`loop`), `preserve` tactic 49:
`have` failed for `buf == (old(buf) + (old(len) - len))`:
proof step tactic 720 > have body tactic 1:
`normalize using` goal did not normalize to true using the listed conditions
```

The related `pinned_zlib_canonical_seed_matches_checked_shared_specification_offline`
test passes after the same unsigned-bound repair, including its own expanded
certificate and negative controls. The short-loop and repeated-block tests
also pass. Preserve those positive controls when reducing this generic
full-stream failure.

This is a tool disagreement, not a reason to increase budgets or weaken the
pointer invariant. Capture and inspect the exact emitted certificate and a
focused trace before changing its planner or checker. Preserve the unchanged
C, locked import, all helper-body checks, and existing negative controls.

Acceptance: the named full-stream test passes, including independent checking
of the complete expansion and its existing mutation controls. Add a reduced
regression retaining the pointer update, native unsigned count subtraction,
and loop snapshot boundaries responsible for the mismatch.
