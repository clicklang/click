# Verifier bugs

One `.md` file per reproduced soundness, proof-tooling, or diagnostic bug,
parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Humans and agents file bugs here without asking; only the
user approves new entries in `issues/`. `AGENTS.md` defines what counts as a
bug, which includes inaccurate and wall-of-text diagnostics. Each file states
the violated invariant, a small intended regression, and acceptance criteria.
Delete a bug file when its fix, regression coverage, and documentation land.

- [Expansion refuses a tactic whose rewrite differs by execution path or obligation](expansion-refuses-path-dependent-rewrites-at-one-leaf.md)
- [Proof failures still print kernel renderings of facts](proof-failures-print-kernel-renderings.md)
- [`simp` exhausts its budget on a false postcondition instead of failing promptly](simp-exhausts-its-budget-on-a-false-list-postcondition.md)
- [A read through an arm identity is not the read through the parameter after a store](arm-identity-read-differs-from-parameter-read-after-a-store.md)
- [A function with early returns verifies in work quadratic in their count](early-return-paths-store-facts-whole.md)
- [A call to an inline helper with a symbolic loop runs away instead of failing](inline-helper-symbolic-loop-call-runs-away.md)
- [Machine-integer quantifiers only support int32](non-int32-machine-integer-quantifiers-are-unsupported.md)
- [Auditing a large claim re-verifies the whole claim for every site](auditing-a-large-claim-reverifies-it-for-every-site.md)
