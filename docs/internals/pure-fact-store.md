# Pure fact store design

`PureFactStore` is the proposed owner of the pure facts available in one proof
scope, their indexes, and their maintained reasoning state. This page records
the agreed ownership boundary and the order of migration; the type is not yet
implemented. The current implementation is described below separately from the
target design.

## Design check

- **Part:** fact store (fast), including the storage used by simple tactics
  and symbolic execution.
- **Why this part:** every checked step needs available facts; this change
  consolidates their representation without adding reasoning or search.
- **Fast reads:** exact and conjunct membership use proposition keys;
  predicate selection uses a predicate key; variable adjacency uses a variable
  key; equality and order reads retain their existing term-keyed indexes.
  Ordered presentation uses a persistent sequence. Successor operations retain
  their explicit deltas instead of finding them by comparing entire stores.
  Each implementation increment must specify the keys for any additional read.
- **Scaling:** proposed regressions at sizes 32, 128, and 512 measure
  deterministic work for fork/append/query with unrelated facts, indexed walks
  over related equality/order chains, and repeated statement transitions.
  Queries must not visit unrelated facts; total chain and transition work must
  stay near-linear up to indexing factors. Preserve the existing
  `explicit_step_scales_near_linearly_with_unrelated_ambient_facts` and
  `sequential_loops_build_the_same_context_entries_each` regressions.
- **Slow:** no new search. Existing smart consumers keep their budgets and
  expansion behavior.
- **Failure:** preserve existing premise refusals and diagnostics. An exact
  membership miss remains a miss; it must not trigger an implicit scan.

The [verifier design rules](verifier-design.md) and
[efficiency contract](verification-efficiency.md) apply to each migration.
This document adds no executable work. Representation changes need their own
focused behavior and scaling validation before delivery.

## Ownership

One store version owns:

- Available pure propositions, including scoped assumptions, in persistent
  storage shared by unchanged branches.
- Their presentation order, including statement-batch priority where callers
  depend on it.
- Exact, conjunct, and other selection indexes required by consumers.
- The maintained reasoning context: equality closure, difference graph, and
  other derived structures currently held by `PureFactContext`.
- Incremental bookkeeping needed to fork, extend, and expose a producer's
  explicit fact delta without rebuilding or comparing complete collections.

Callers introduce facts through store operations. Those operations construct
the successor store and maintain its affected indexes and reasoning state;
callers do not independently update a proposition list and an assumptions
context. Internal indexes may retain references to propositions. The goal is
one owner of available facts, with multiple query representations inside it.

The central invariant is that a store version presents exactly the facts
available in its scope, and all its indexes and reasoning structures describe
that version. Derived reasoning consequences need not become additional
explicit entries. Preserve the distinction between a top-level fact and a
proper conjunct available for extraction.

The proof or execution operation introducing an assumption establishes its
scope. The store records that assumption and supports reasoning under it;
storage does not establish its justification. Branches and nested proofs have
their own versions, and local assumptions must not leak into siblings or
parents. This is not a global collection of everything ever established.

## Boundaries with other state

| Component | Responsibility |
| --- | --- |
| `PureFactStore` | Available pure propositions and indexed reasoning under them. |
| `ResourceContext` | Resource ownership, permissions, and resource algebra. |
| Memory state | Symbolic contents, immutable snapshots, and memory derivations. |
| Program structure and execution frontier | Statements and regions, plus the current position and pending continuations. |

Facts can refer to values, memory snapshots, and resources without owning those
systems. The proof/execution state coordinates these components. This proposal
does not reorganize program structure, memory, or resources, and does not
require execution state to become one new aggregate type.

The store does not own proof goals, certificates, or execution history. A
proposition's availability is distinct from the evidence establishing it.
Transitions and derivations retain certification, transport, and producer
metadata; equal propositions do not imply interchangeable evidence. References
from evidence to stored facts must remain valid across persistent versions.
Classify individual `ExecutionPureFact` fields before changing their storage;
do not discard evidence as duplicate merely because its proposition is present.

## Current overlap

| Current type | Relevant responsibilities | Source |
| --- | --- | --- |
| `PureFactList` | Ordered propositions, exact/conjunct index, cached context, and retained source `ProofFacts`. | `src/surface/pure_fact_list.rs` |
| `ProofFacts` | Ordered propositions, proof selection indexes, variable reservations, and reasoning contexts. | `src/kernel/proof/facts.rs` |
| `PureFactContext` | Assumed facts and maintained reasoning indexes/graphs. | `src/kernel/primitives.rs`, `src/kernel/assumptions.rs` |
| `ExecutionFacts` | Ordered execution evidence and membership indexes. | `src/kernel/execution_facts.rs` |

`PureFactList::from_proof_facts`, `extended_to_proof_facts`, and `proof_facts`
already preserve contexts and synchronize shared prefixes. They identify the
first migration boundary. Preserve the checked context's lineage, including
its association with resources; replaying equal propositions into a fresh
context is not a substitute for retaining that context.

## Migration order

1. **Map one statement transition.** Trace `ProofFacts` into `PureFactList`,
   through a certified statement transition, and back into `ProofFacts`.
   Record each consumer's ordering, scope, evidence, and query requirements,
   and each copy, rebuild, or reindex. Include a branch and a transported
   memory fact. Completion: a source-backed operation/ownership map that
   determines the first store interface and focused regressions.
2. **Extract the kernel store from `ProofFacts`.** Move proposition ownership,
   common indexes, and the retained reasoning context into `PureFactStore`.
   Delegate existing operations to it; keep proof-specific evidence and
   metadata outside. Classify variable reservations and specialized indexes
   by whether they are derived from available facts or specific to a proof
   operation. Completion: `ProofFacts` no longer separately owns the migrated
   facts or maintains a second copy of their indexes/context.
3. **Share the store through the selected statement path.** Make its Surface
   consumers use the same persistent store, with thin views where needed.
   Replace the selected `PureFactList` conversion/synchronization path and
   remove the storage it duplicates. Completion: one statement transition
   carries a shared store throughout and updates it only by its fact delta.
4. **Migrate remaining list consumers.** Cover loops, calls, nested proofs,
   branch joins, and smart planning. Preserve explicit ordering, scoped
   assumptions, and context lineage. Completion: remove `PureFactList`'s
   independent storage and prefix-synchronization machinery; make
   `PureFactContext` an internal reasoning component reached through the store.
5. **Integrate execution publication.** Separate available propositions from
   execution evidence and share proposition storage where scope permits.
   Retain evidence-specific order, certification, transport, and producer
   identity. Completion: publication does not rebuild an already retained
   fact context or maintain another available-fact owner for the same scope.
6. **Close remaining reconstruction paths.** Replace internal flatten/rebuild
   APIs with store handles, indexed queries, or explicit deltas. Keep full
   enumeration for consumers such as printing or bounded smart search that
   actually need it. Completion: each remaining collection has an explicit
   role as an index, view, different scope, or evidence sequence.

Deliver coherent increments in this order. Each storage extraction must remove
the old ownership at its migrated boundary; a wrapper around unchanged owners
does not complete a stage. Exact API names, fact handles, deletion support,
and eager versus lazy index construction remain implementation decisions to
resolve from the operation map.

## Validation and first milestone

For code changes, test exact membership, top-level versus proper-conjunct
authority, ordering, branch isolation, nested-assumption scope, and preservation
of checked memory/evidence identity where affected. Check proof expansion
round trips on the migrated path. Add deterministic scaling coverage for
unrelated input, related chains, and repeated transitions, including copies
and context rebuilds that existing counters expose.

The first implementation milestone is stages 1 through 3: one statement
transition uses a shared `PureFactStore` through planning and checked proof
construction, with its former duplicate storage removed. Broader migration
follows once this path preserves behavior and meets the cost contract.
