# Verifier bugs

One `.md` file per reproduced soundness, proof-tooling, or diagnostic bug,
parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Humans and agents file bugs here without asking; only the
user approves new entries in `issues/`. `AGENTS.md` defines what counts as a
bug, which includes inaccurate and wall-of-text diagnostics. Each file states
the violated invariant, a small intended regression, and acceptance criteria.
Delete a bug file when its fix, regression coverage, and documentation land.

- [Expanded `simp` in a loop `initialize` emits an arithmetic step the checker rejects](loop-initialize-expansion-emits-rejected-arithmetic-certificate.md)
- [Expansion loses the facts a later call precondition needs](expansion-drops-call-precondition-evidence.md)
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
- [A function-level `match` arm cannot close by `contradiction` after a `have`](function-match-arm-rejects-contradiction-after-have.md)
- [A refused arm `contradiction` is reported at an unrelated earlier tactic](arm-contradiction-refusal-names-an-unrelated-tactic.md)
- [The refusal of `old(c.model)` in a loop clause suggests a binding that is rejected](loop-clause-old-field-refusal-suggests-a-rejected-unfold-binding.md)
- [`simp` exhausts its budget on a false postcondition instead of failing promptly](simp-exhausts-its-budget-on-a-false-list-postcondition.md)
- [A read through an arm identity is not the read through the parameter after a store](arm-identity-read-differs-from-parameter-read-after-a-store.md)
- [`--trace-proof` prints no trace when the failure is a loop frontier report](trace-proof-prints-no-trace-at-a-loop-frontier.md)
- [Loop `break` exits that reach the same state in a different representation do not join](loop-exits-equal-up-to-representation-do-not-join.md)
- [Connected-fact selection indexes the context once per context, not incrementally](connected-fact-selection-indexes-the-context-per-derivation.md)
