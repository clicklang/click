# Proposition candidate selection scans unrelated facts

## Violated invariant

Selecting a source for one memory or resource derivation should read indexed
candidates for that goal, not every ambient proposition. In
`src/surface/planning/proposition_search.rs`, `atomic_derivation_premises`
calls `proposition_facts().filter(candidate_family)` for
`CMemoryReadDefined`, `CMemoryLoadable`, `CMemoryCanStore`, and
`CResourceSeparate` goals. The family predicate is broad: even a fixed goal
visits unrelated facts of the same kind. The planner then tries candidates
one at a time and, for loadability, pairs of candidates. This is bounded
smart search but can grow with unrelated proof state and repeatedly invoke
the checked atomic query.

This selection problem is distinct from the cost of constructing each trial
context, which is tracked in `atomic-evidence-retains-ambient-context.md`.

## Intended regression

Use one fixed loadability goal with one valid source range, then add many
unrelated loadability ranges of the same proposition family at multiple
sizes. Repeat with a goal requiring two adjacent source ranges and with a
resource-separation goal. Measure candidate visits and complete derivation
work deterministically; include negative candidates that share a broad kind
but cannot justify the goal. Check the selected certificate and its expansion
and re-verification.

## Acceptance criteria

- Candidate lookup uses goal-specific indexes or sound necessary-condition
  keys, so unrelated same-family facts are not visited by each fixed query.
  Any fallback bucket has a documented completeness reason and a scaling
  regression.
- Pair trials are limited to candidates that could jointly justify the
  selected loadability rule; the planner does not try all unrelated pairs.
- The kernel remains the authority for each candidate's validity. Positive,
  negative, snapshot, and resource cases retain their current answers, and
  the retained certificate names the successful source facts.
- `scripts/check.sh` passes. This bug is not an e-graph migration prerequisite
  unless a concrete migrated consumer exposes it.
