# One fact-aware frame query instead of scattered history walks

Priority: P1.

Soundness: not soundness. This is performance and design: every walk named
here is checked, and none is known to accept a false claim. The issue is
that one question is answered by several different searches, at different
costs, from many places in simple checking.

## The question and how it is answered today

"Does cell `c` hold the same value at points `P` and `Q` on this path?" has
two answers in the kernel. The version walk (`resource_tracker::last_same_point`)
answers it without facts: it walks back from a snapshot, crosses every step
that provably does not write `c`'s bytes, and is memoized per (snapshot,
address, width). Lowering uses only this walk, and it is cheap.

When the answer needs the path's facts (a `separate` premise, ownership, an
alias equality), the fact-aware walk (`memory_dag_cell_source` with the
path's assumptions) answers it. Its result depends on facts, so it is not
memoized by snapshot. It now resumes the memoized version walk at every
step and applies facts only where that walk stopped, recording the crossed
prefix as one `SameVersion` hop; the scaling regression
`a_fact_aware_cell_walk_resumes_the_memoized_version_walk` measured it
quadratic in history length before. It is still reached through eight entry
points with four different walk modes:

- full walk with extended bridging and an explicit DAG check:
  `memory_provenance::complete_pointer_read_value` and
  `complete_pointer_carrier_read_value`;
- resume the memoized version walk and apply facts only where it stopped:
  `resource_tracker::cell_value_on_path`;
- bounded to 64 steps: `memory_provenance::bounded_recorded_cell_resolution`;
- checked-endpoint packaging: `checked_pointer_read_endpoint`,
  `checked_pointer_read_stored_value`, and the derivation searches
  `explicit_atomic_equality_from_memory_derivations`,
  `resolve_load_along_memory_derivations` and
  `checked_call_load_equality_evidence`.

Their callers are spread through simple checking:

- C execution: `evaluate_c_memory_load_case` (through
  `cell_value_recorded_on_path`), `canonicalized_pointer_value_from_int_cell`,
  `canonicalized_symbolic_load_value_with_identity`, and
  `add_normalized_verified_ensure_facts` after a call;
- exact fact lookup: `ProofFacts::with_checked_rewritten_loads`
  (`checked_stored_origin_equality`);
- the equality-graph rebuild: `rebuild_algebraic_graph_equalities` through
  `PureFactContext::pointer_designations_match`;
- resource matching: `memory_fact_candidates`, `graph_for_memory_query`,
  `loads_bridged`, `bitvectors_match_for_resource_check`, and
  `resource_body_fact_is_established`;
- frames: `quantified_frame::loads_unchanged`;
- contract certification: `names_of_one_cell_framed` and
  `pointer_offsets_equal_with_resolved_atoms`;
- wide reads: `wide_read_observations_have_value`,
  `narrow_read_has_recorded_value`, and `read_is_of_a_recorded_store`.

So whether two reads are related, and what it costs to find out, depends on
which check asks. The [verification efficiency
contract](../docs/internals/verification-efficiency.md) requires simple
checking to scale with the relevant state delta; with four walk modes that
is hard to state, let alone test.

## Relation to pointer reads named by version

[Spellability](../docs/internals/spellability.md) requires a logical pointer
read to lower to the read at its version, never to the pointer a cell
stores. On master, logical lowering folds a pointer read to its stored
pointer through `complete_pointer_read_value`, which consults facts: a known
violation. Removing the fold does not depend on this item. Where the
fact-free version walk cannot cross a store, two reads of one unchanged cell
are two versions, and the proof states the frame that relates them (for
example, the `pop` of a recursive stack needs `node->next` related across a
store through `self.head` before its `fold`). Proofs change; the kernel does
not search for the frame on their behalf. Adding fact-aware walks inside
individual checks to keep the old proof text working is the scattering this
item removes, and must not be done.

## Intended regression and acceptance criteria

- One function answers the frame question for a cell between two points on
  a path, in the resume-the-version-walk form: the memoized version walk
  crosses what it can without facts, and facts are applied only at the steps
  where it stopped.
- Every call site above routes through it, one group at a time, and the
  other entry points and walk modes are deleted as their callers move.
- A deterministic scaling regression in `src/scaling_tests/` measures the
  function across history lengths and unrelated state sizes, and shows work
  bounded by the steps where the version walk stops, not by history length.
- No check calls a fact-aware walk except through the one function.
