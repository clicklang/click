# Verifier bugs

One `.md` file per confirmed or strongly evidenced soundness or proof-tooling
bug, parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Each file states the violated invariant, a small intended
regression, and acceptance criteria. Delete a bug file when its fix, regression
coverage, and documentation land.

- [Atomic evidence rebuilds and retains ambient contexts](atomic-evidence-retains-ambient-context.md)
- [`auto` expansion re-verifies against a callee with no verified clause](auto-expansion-loses-callee-contract-clauses.md)
- [Expanded `simp` in a loop `initialize` leaves the invariant entry goal open](loop-initialize-expansion-does-not-close-entry-goal.md)
- [Expanded `simp` in a loop `initialize` emits an arithmetic step the checker rejects](loop-initialize-expansion-emits-rejected-arithmetic-certificate.md)
- [Expanded `simp` in a loop `initialize` emits a tactic after one that closed the goal](loop-initialize-expansion-continues-after-closing-tactic.md)
- [Expansion loses the facts a later call precondition needs](expansion-drops-call-precondition-evidence.md)
- [Expanded proofs about file-scope and static objects do not re-verify](expanded-static-object-proofs-do-not-reverify.md)
- [Expansion of a by-value struct copy emits a `have` that lowers to zero paths](expansion-emits-have-that-lowers-to-no-path.md)
- [Expanded `simp` emits an `assumption` that matches no goal](simp-expansion-assumption-matches-no-goal.md)
- [Expansion refuses a witness that has no surface spelling](expansion-needs-unspellable-resource-witness.md)
- [Expansion is unavailable where a call has an exceptional path](expansion-unavailable-for-exceptional-call-paths.md)
- [Expanded sidecar prints a multidimensional array field with too few indices](expanded-sidecar-misprints-multidimensional-array-fields.md)
- [Expansion refuses a tactic whose rewrite differs by execution path or obligation](expansion-refuses-path-dependent-rewrites-at-one-leaf.md)
- [Expanded proof no longer certifies termination](expansion-loses-termination-evidence.md)
- [Expanded proof no longer certifies a `produces` claim](expansion-loses-produced-resource-claim.md)
- [Expansion changes what a later C branch condition is decided from](expansion-changes-branch-condition-decision.md)
- [`click audit` cannot resolve an `ensures` source it inventoried](audit-cannot-resolve-ensures-source.md)
- [Proof failures still print kernel renderings of facts](proof-failures-print-kernel-renderings.md)
