# Connected-fact selection indexes the context once per context, not incrementally

## Violated invariant

A smart atomic derivation should spend work on the facts related to its goal,
not on the size of the ambient context. In
`src/surface/planning/proposition_search.rs`, `fact_connection_variables`
collects the connection variables of every condition and proposition fact of
a context, and `ConditionIndex::new` and `connected_facts` then build a
variable-to-fact map over all of them before walking the goal's component.

The per-fact variables are cached for the sixteen most recently asked
contexts, keyed by the context's content identity, so one context is
collected once however many goals are asked of it. But a context that
differs by one fact from a cached one is collected whole again, the
variable-to-fact map is rebuilt for every derivation, and the cache is a
bounded list scanned linearly. A proof that extends its context by one fact
per step therefore pays work proportional to the whole context at each step.

This is planner cost. The selection only chooses premises; the kernel checks
the derivation from whatever was selected.

## Intended regression

Grow a context one unrelated fact at a time, asking one fixed connected goal
after each addition, at several deterministic sizes. Measure the facts
visited to build the selection apart from kernel checking work, and assert
that the total over the run is near-linear in the number of additions rather
than quadratic. Include a goal that reaches the widened selection.

## Acceptance criteria

- The variable-to-fact relation is maintained with the context, or derived
  incrementally from a parent context's, so adding a fact costs work
  proportional to that fact.
- Selecting a goal's connected facts costs work proportional to the
  component selected, up to indexing factors.
- The selected premises, and therefore every certificate, are unchanged.
  The multi-size regression pins the scaling and `scripts/check.sh` passes.
