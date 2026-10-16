# Zlib full-stream expansion loses a pointer invariant proof

Soundness: not soundness. The original full-stream contract and its helper
bodies verify against the locked, unchanged C source, but rechecking its
expanded certificate fails. No false acceptance is known.

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
