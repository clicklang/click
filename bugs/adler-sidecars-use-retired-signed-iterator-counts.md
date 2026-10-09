# Adler sidecars still observe retired signed iterator counts

The native Charon adapter now keeps chunk and scalar iterator remaining counts
as full-width `usize` (`uint64` on the pinned target). The unchanged Adler
general sidecar still asserts the former implicit `int32` projection. This breaks the
published general whole-body bounds proof even for its explicitly bounded input domain.

Reproduced twice on upstream `91d54ac32`, with the original pinned adler2 source,
artifact, and import lock unchanged:

```
cargo test --test rust_import \
  charon_adler2_general_compute_proves_original_body -- --include-ignored
```

The first failure is computation tactic 18, asserting
`__rust_mir_27_remaining == (int32)(uint32)(prefix - prefix % 22208u64)`.
The actual remaining value now equals the full-width bulk length. The selected
contract's `bytes_len <= 2147483647u64` condition remains valid; it does not by
itself supply a checked equality between the two observations to `simp`.

Acceptance:

- Port the canonical Adler sidecars to actual native remaining counts, with
  explicit bounds and checked projections where the mathematical library still
  takes signed indices. Do not narrow native iterator state or edit Rust source.
- Restore whole-body bounds/termination, existing small boundaries, and
  verify/profile/expanded-proof agreement for the locked computation.
- Keep missing authority, bad seeds, false iterator states, and false output
  claims rejected. Do not raise budgets or disable checks to make proofs pass.
- Keep the roadmap and trial documentation accurate about the proved boundary.
