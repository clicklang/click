# Linked owned-field stores charge per unrelated parameter

Soundness: not soundness. All native programs verify their intended final
values, but per-store deterministic work grows with unrelated owned objects.
No false proof acceptance was observed.

Reproduced with production master `67a990f30b00941cf1f7d7e270a7bcdd57e70230`
(test tree `3fa7a376372ba92954a6629de0742501a02a5ea6`), Rust 1.98.1, ordinary
unoptimized profile, using the unchanged regression:

```sh
RUST_MIN_STACK=8388608 cargo test --lib \
  surface::tests::scaling_tests::owned_parameter_field_store_work_is_flat \
  -- --exact --ignored --nocapture
```

The test is in `src/scaling_tests/surface/tests/scaling_tests.rs`. It verifies
nine full native C programs: plain fields, linked fields, and plain fields
with repeated modular calls, each at 4, 16, and 64 stores. Every pointer
parameter is independently owned before any store. In the linked family,
the program sets `p0->next = p1`, and so on, sets the final node's value to 9,
calls the unchanged `touch` helper, reads the complete linked chain, and
proves the result is 9. Keep that source pattern.

The peak work charged to a field-store `step` is:

| Family | N=4 | N=16 | N=64 |
|---|---:|---:|---:|
| Plain fields, one call | 127 | 127 | 127 |
| Linked fields, one call | 784 | 796 | 844 |
| Plain fields, repeated calls | 127 | 127 | 127 |

The linked peaks are exactly `780 + N`, violating the existing allowance
`peak(N) <= peak(4) + 32` at N=64. The linked call peaks are 3018, 3027,
and 3027; plain call peaks stay constant within their families. The failure
is the store-work assertion, not verification or a time limit.

The whole baseline took about 48.6 seconds. It is excluded from test-saving
measurements; shrinking its maximum could conceal the defect.

Acceptance criteria:

- Make linked-field store work independent of unrelated owned parameters,
  subject only to the documented indexing factors.
- Pass the original 4/16/64 regression without relaxing the work allowance,
  dropping the 64-node chain, or changing the native C pattern.
- Retain all three program families, repeated calls, complete chain reads,
  checked results, and per-call work bounds.

Confirmed again on upstream `465b0af319e98541134378a0aee81aa938b72572`; the same work values and assertion failure persist after the independent pointer-offset and call-requirement fixes.
