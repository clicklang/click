# Audit checks a partial claim rewrite with the implicit auto off

Soundness: not soundness. The audit refuses a valid rewrite; it accepts
nothing false.

`6036f8e79` ("Check whole-claim expansions with the implicit auto off") says
a whole claim's expansion is cold-verified without the implicit `auto`, while
"a single site's expansion is still checked warm, since the claim's other
steps and smart tactics use the implicit auto". The change wraps the cold
verification in `audit_selected_claim_rewrite` (`src/bin/click-audit.rs`), the
path for a claim that a cursor, a change selection or `--max-sites` covers
only in part. `audit_claim_rewrite`, the whole-claim path, is unchanged. A
partial rewrite keeps the claim's unselected smart tactics, and those that
need the implicit `auto` now fail the audit.

Reproduced on `7f2047bfd` by the nightly test
`adler2_helpers::charon_adler2_helpers_mul_audit_simp_certificate`
(`tests/rust_import/adler2_helpers.rs`). It audits only the `simp()` site of
the `MulAssign<u32>` proof in `design/charon-trial/adler2/helpers.click`
(`click audit --start-at <simp() line> --max-sites 1`). The proof starts with
`execute();`, whose Rust multiplication panic check
(`rhs == 0u32 or x <= 4294967295u32 / rhs`) the implicit `auto` closes. The
audit fails with:

```text
`__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32.contract` tactic 0:
`execute()` is missing prerequisite (Rust mul panic check): could not show
`((__rust_checked_2 as u32) == 0u32) || ((__rust_checked_1 as u32) <= ...)`
from the fact `__rust_checked_2 != 0u32`
SUMMARY: 0 sites passed; 0 site failures; 1 claim failures; ...
```

The same site expanded by `click expand <sidecar>:<line>:<column> --in-place`
verifies with `click verify`, and the whole-claim
`click expand --claim ...mul_assign_u32.contract` succeeds with the implicit
`auto` off. Only the audit's partial-selection check disagrees.

Acceptance:

- `audit_selected_claim_rewrite` checks a partial rewrite warm, as before
  `6036f8e79`. `audit_claim_rewrite` checks a whole claim's expansion with the
  implicit `auto` off.
- `charon_adler2_helpers_mul_audit_simp_certificate` passes again, and a
  whole-claim audit still refuses an expansion that needs the implicit `auto`.
