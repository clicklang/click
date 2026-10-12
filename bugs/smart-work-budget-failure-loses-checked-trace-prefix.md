# Smart work-budget failure loses the checked trace prefix

When a `have ... by simp()` inside the Adler2 remainder loop exhausts its
existing deterministic tactic work budget, `verify --trace-proof` reports
“proof trace unavailable: no checked path was retained for this failure”. The
same construction has a checked prefix containing the iterator advance,
constructor call, and its postconditions. A prompt proof refusal retains that
prefix and exposes the snapshot mismatch; the budget failure should retain it
as well. This prevents the normal trace workflow from explaining the failed
comparison without reproducing an earlier refusal.

Reproduction in the pinned unchanged Adler2 trial:

1. Assemble `GENERAL_COMPUTE` with `compute_proof` and `compute_project` in
   `tests/rust_import/adler2_helpers.rs`, which also supplies its unchanged
   source, locked import, and checked helper libraries.
2. In the `loop(2)` preserve body, immediately after `mark vector_a`, insert:

   ```click
   have at(vector_a, __rust_mir_68.0[0]) ==
       at(vector_a, (__rust_mir_69[0] as u32)) by simp();
   ```

3. Run ordinary verification and
   `click verify --trace-proof adler2::Adler32::compute borrow.click` against
   the assembled project. The reproduced run exhausts 2,000,001 smart work
   units against the unchanged 2,000,000-unit limit and emits no trace prefix.

The successful proof uses the constructor's call-entry Integer postcondition,
rather than this untransported post-call machine-byte comparison. No increase
of limits is needed or requested.

Acceptance criteria: retain the checked prefix and failing comparison for
budget failures inside nested `have` and loop bodies, keep trace rendering
bounded by the retained events, and preserve the existing proof verdicts and
work limits. Add a reduced regression that does not depend on wall-clock time.
