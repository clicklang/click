# Finish the equality service: delete the overlapping equality stores

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. The trusted
kernel keeps about ten stores that each answer some form of "are these two
terms equal", all fed from the same condition facts. Each derivation has to
be reviewed separately, and two stores can give different answers to the
same question. `docs/internals/equality-closure.md` states the goal this
violates: "A proved equality must have the same meaning at every kernel
consumer."

P1 by user direction (2026-10-16).

## Current state and violated invariant

`docs/internals/equality-closure.md` chose "one persistent equality service in
the kernel, using congruence closure without saturation", and the
`equality_graph` (`src/kernel/equality_graph.rs`) now serves int32 Boolean
queries. Its retirement table lists what is still to be deleted, and says
"Full deletion is an acceptance criterion, not optional cleanup." These
`PureFactContext` fields (`src/kernel/primitives.rs`) still hold equalities
beside the graph:

- `bitvector_equality_facts`, the lazy exact-equality index, rebuilt by a
  scan of every condition fact. It still serves
  `bitvector_equality_class` and `exact_bitvector_equality_path_evidence`
  in decision, `simp`, order paths, resource algebra and proposition
  reasoning;
- `bitvector64_equality_facts`, the 64-bit adjacency map;
- `constant_classes` (`ConstantClasses`, its own union-find),
  `direct_bitvector_equalities` and `exact_constant_equalities`;
- `pointer_block_aliases`, `pointer_block_aliases_by_offset`,
  `pointer_alias_endpoints_by_object`,
  `wide_pointer_alias_endpoints_by_object`, `pointer_offset_aliases` and
  `pointer_offset_aliases_by_root`, read through `exact_pointer_aliases` and
  similar accessors at about 50 sites;
- `algebraic_constructor_field_equalities`, beside the graph's algebraic
  congruence.

The overlap shows in the code:

- every condition insert updates about ten stores, and withdrawal has more
  than one rebuild path;
- `rebuild_equality_graph` (`src/kernel/assumptions.rs`) refiles from
  `pointer_block_aliases` and `pointer_offset_aliases`, so on withdrawal the
  legacy stores are the graph's source of truth, not the other way round;
- `uint64_values_equal_for_range_resolution` asks the graph, then the 64-bit
  adjacency map, and `recorded_uint64_equals` then falls back to a scan of
  every condition fact;
- some fast paths switch off globally when a legacy store is non-empty
  (`simp.rs` when any 64-bit equality exists; `parameter_store_partition`
  in `memory_reasoning.rs` when any offset alias exists);
- `decision.rs` uses `constant_classes` as a negative shortcut and then walks
  `direct_bitvector_equalities`.

The invariant: one equality service answers every equality question,
including alias enumeration, premise-path evidence and constant discovery,
for every theory the kernel has (int32, uint64, pointers, algebraic values).
The other stores are deleted, not kept as caches beside it.

## Intended regression

Keep the graph scaling suites (`src/scaling_tests/kernel/equality_graph/*`)
and the 39 assertions that the lazy index is never built
(`bitvector_equality_index_fact_visits() == 0`). Add scaling regressions for
the paths that still scan: a uint64 equality chain resolved for a range, a
constant discovered through a chain of equalities, and alias enumeration over
many pointer equalities. Each must grow linearly with the facts it uses, not
with all facts. Add mdtests for a 64-bit equality and a pointer-offset alias
that today switch off the global fast paths.

## Acceptance criteria

- Every store listed above is removed from `PureFactContext`, or kept only as
  a documented input that the equality service owns.
- Alias enumeration, premise-path evidence and constant discovery are
  queries on the equality service.
- Withdrawal rebuilds the service from its own inputs, not from legacy
  stores.
- The retirement table in `docs/internals/equality-closure.md` is empty, and
  the document describes the single service.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
