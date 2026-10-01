# Verifier bugs

One `.md` file per confirmed or strongly evidenced soundness or proof-tooling
bug, parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Each file states the violated invariant, a small intended
regression, and acceptance criteria. Delete a bug file when its fix, regression
coverage, and documentation land.

- [Condition premise selection repeatedly scans ambient facts](condition-premise-selection-scans-ambient-facts.md)
- [Proposition candidate selection scans unrelated facts](proposition-candidate-selection-scans-unrelated-facts.md)
- [Atomic evidence rebuilds and retains ambient contexts](atomic-evidence-retains-ambient-context.md)
- [Narrow integer parameters lack their type range at entry](narrow-parameters-lack-their-type-range.md)
- [`simp` and `arithmetic()` stop at short order chains](unsigned-and-long-order-chains-in-simp-and-arithmetic.md)
- [A refused store through a widened unsigned index doesn't name the element](store-refusal-through-unsigned-index-names-no-element.md)
- [Whole-path refusals don't name a C statement](whole-path-refusals-lack-a-statement-location.md)
- [`simp` and `arithmetic()` treat sign-bit-flipped unsigned values as opaque](unsigned-order-arithmetic-in-closers.md)
- [A ranked loop whose body branches loses its decrease member](branching-loop-body-ranking-member-not-certified.md)
