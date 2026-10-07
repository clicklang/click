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
- [Whole-claim expansion misplaces shared tactics in a nested `__rb_insert` match](whole-claim-expansion-fails-on-proof-matches.md)
- [Whole-claim expansion adds outcome tactics to a pruned C branch](pruned-returning-branch-expansion-adds-unbound-result.md)
