# Verifier bugs

One `.md` file per reproduced soundness, proof-tooling, or diagnostic bug,
parallel to `issues/`: these are defects filed for a fixer rather than
roadmap milestones. Humans and agents file bugs here without asking; only the
user approves new entries in `issues/`. `AGENTS.md` defines what counts as a
bug, which includes inaccurate and wall-of-text diagnostics. Each file states
the violated invariant, a small intended regression, and acceptance criteria.
Delete a bug file when its fix, regression coverage, and documentation land.

- [A retained verification session cannot re-verify a caller it already verified](retained-session-cannot-reverify-a-verified-caller.md)
- [Expansion refuses a witness that has no surface spelling](expansion-needs-unspellable-resource-witness.md)
- [`loop` expansion emits an empty `by` block](loop-expansion-emits-empty-by-block.md)
- [Expansion is unavailable where a call has an exceptional path](expansion-unavailable-for-exceptional-call-paths.md)
- [Expansion refuses a tactic whose rewrite differs by execution path or obligation](expansion-refuses-path-dependent-rewrites-at-one-leaf.md)
- [Expanded proof no longer certifies a `produces` claim](expansion-loses-produced-resource-claim.md)
- [Expansion changes what a later C branch condition is decided from](expansion-changes-branch-condition-decision.md)
- [Proof failures still print kernel renderings of facts](proof-failures-print-kernel-renderings.md)
- [A function-level `match` arm cannot close by `contradiction` after a `have`](function-match-arm-rejects-contradiction-after-have.md)
- [A refused arm `contradiction` is reported at an unrelated earlier tactic](arm-contradiction-refusal-names-an-unrelated-tactic.md)
- [The refusal of `old(c.model)` in a loop clause suggests a binding that is rejected](loop-clause-old-field-refusal-suggests-a-rejected-unfold-binding.md)
- [`simp` exhausts its budget on a false postcondition instead of failing promptly](simp-exhausts-its-budget-on-a-false-list-postcondition.md)
- [A read through an arm identity is not the read through the parameter after a store](arm-identity-read-differs-from-parameter-read-after-a-store.md)
- [`--trace-proof` prints no trace when the failure is a loop frontier report](trace-proof-prints-no-trace-at-a-loop-frontier.md)
- [Connected-fact selection indexes the context once per context, not incrementally](connected-fact-selection-indexes-the-context-per-derivation.md)
- [A function with early returns verifies in work quadratic in their count](early-return-paths-store-facts-whole.md)
- [A loop proof's certificate merge costs uncounted work that grows faster than the proof](loop-proof-certificate-merge-costs-uncounted-superlinear-work.md)
- [Expanded `simp` emits an `assumption` that matches no goal](simp-expansion-assumption-matches-no-goal.md)
- [An error in the standard library is reported against the user's module](standard-library-error-names-the-user-module.md)
- [A struct retyping cast diagnostic omits the struct tags](struct-retyping-cast-diagnostic-omits-struct-tags.md)
