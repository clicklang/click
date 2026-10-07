# Verifier bugs

One `.md` file per reproduced soundness, proof-tooling, or diagnostic bug,
parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Humans and agents file bugs here without asking; only the
user approves new entries in `issues/`. `AGENTS.md` defines what counts as a
bug, which includes inaccurate and wall-of-text diagnostics. Each file states
the violated invariant, a small intended regression, and acceptance criteria.
Delete a bug file when its fix, regression coverage, and documentation land.

- [A function with early returns verifies in work quadratic in their count](early-return-paths-store-facts-whole.md)
- [Auditing a large claim re-verifies the whole claim for every site](auditing-a-large-claim-reverifies-it-for-every-site.md)
- [Pointer arithmetic past an object of unknown size is accepted without an obligation](pointer-arithmetic-past-unknown-size-object-is-unchecked.md)
- [A one-past-the-end pointer is proved unequal to every other object's start](one-past-end-pointer-decided-unequal-to-adjacent-object.md)
- [int32 division by a symbolic divisor is refused as signed overflow](int32-symbolic-divisor-refused-as-signed-overflow.md)
- [A nested loop with an inner `break` is refused under concrete execution](nested-loop-inner-break-refused-under-concrete-execution.md)
- [A decidably false return narrowing reports an internal error, not the range](false-return-narrowing-reports-internal-error.md)
- [`requires x != INT_MIN` does not discharge the overflow of `-x`](negation-not-discharged-by-int-min-disequality.md)
- [A parent cannot lock its own mutex after joining a typed `mutex_use` worker](mutex-lock-after-joining-typed-worker-refused.md)
- [A natural `goto` cycle's forward `goto` exit is dropped, so the contract is vacuous](natural-goto-cycle-forward-exit-is-dropped.md)
