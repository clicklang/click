# Verifier bugs

One `.md` file per confirmed or strongly evidenced soundness or proof-tooling
bug, parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Each file states the violated invariant, a small intended
regression, and acceptance criteria. Delete a bug file when its fix, regression
coverage, and documentation land.

- [Condition premise selection repeatedly scans ambient facts](condition-premise-selection-scans-ambient-facts.md)
- [Proposition candidate selection scans unrelated facts](proposition-candidate-selection-scans-unrelated-facts.md)
- [Atomic evidence rebuilds and retains ambient contexts](atomic-evidence-retains-ambient-context.md)
- [`simp` and `arithmetic()` stop at short order chains](unsigned-and-long-order-chains-in-simp-and-arithmetic.md)
- [`arithmetic() using` does not use the unsigned order lemmas](unsigned-order-arithmetic-in-closers.md)
