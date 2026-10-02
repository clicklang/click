# Verifier bugs

One `.md` file per reproduced soundness, proof-tooling, or diagnostic bug,
parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Humans and agents file bugs here without asking; only the
user approves new entries in `issues/`. `AGENTS.md` defines what counts as a
bug, which includes inaccurate and wall-of-text diagnostics. Each file states
the violated invariant, a small intended regression, and acceptance criteria.
Delete a bug file when its fix, regression coverage, and documentation land.

- [A retained verification session cannot re-verify a caller it already verified](retained-session-cannot-reverify-a-verified-caller.md)
- [Expanded proofs about file-scope and static objects do not re-verify](expanded-static-object-proofs-do-not-reverify.md)
- [Expansion of a by-value struct copy emits a `have` that lowers to zero paths](expansion-emits-have-that-lowers-to-no-path.md)
- [Expanded `simp` emits an `assumption` that matches no goal](simp-expansion-assumption-matches-no-goal.md)
- [Expansion refuses a witness that has no surface spelling](expansion-needs-unspellable-resource-witness.md)
- [`loop` expansion emits an empty `by` block](loop-expansion-emits-empty-by-block.md)
- [Expansion is unavailable where a call has an exceptional path](expansion-unavailable-for-exceptional-call-paths.md)
- [Expansion refuses a tactic whose rewrite differs by execution path or obligation](expansion-refuses-path-dependent-rewrites-at-one-leaf.md)
- [Expanded proof no longer certifies termination](expansion-loses-termination-evidence.md)
- [Expanded proof no longer certifies a `produces` claim](expansion-loses-produced-resource-claim.md)
- [Expansion changes what a later C branch condition is decided from](expansion-changes-branch-condition-decision.md)
- [Proof failures still print kernel renderings of facts](proof-failures-print-kernel-renderings.md)
- [Connected-fact selection indexes the context once per context, not incrementally](connected-fact-selection-indexes-the-context-per-derivation.md)
- [A function with early returns verifies in work quadratic in their count](early-return-paths-store-facts-whole.md)
