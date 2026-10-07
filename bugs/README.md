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
- [Whole-claim expansion fails on counted populations, a loop `branch`, `sort3` and `__rb_insert`](whole-claim-expansion-fails-on-proof-matches.md)
- [Differing natural goto exit states leave joined facts without Click spellings](natural-goto-exit-join-facts-cannot-be-spelled.md)
- [A natural cycle with return and forward goto exits cannot expand](natural-goto-mixed-return-exit-expansion-loses-path-coverage.md)
- [A loaded tagged null word cannot convert back to a pointer](tagged-null-load-cannot-convert-to-pointer.md)
