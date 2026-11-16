# Pure fact store design

`PureFactStore` owns the pure facts available in one proof scope, their indexes,
and their maintained reasoning state. The first implementation extracts that
ownership from `ProofFacts` and shares it through the ordinary statement path.
This page records the ownership boundary, the mapped statement transition,
and the remaining migration order. Legacy list consumers still exist.

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
Representation changes need focused behavior and scaling validation before
delivery. The statement-store regression
`statement_store_views_only_index_their_delta` grows ambient facts and fork
count together at sizes 32, 128, and 512 and counts copies, indexed entries,
and context rebuilds.

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

## Storage extraction

`PureFactStore` in `src/kernel/proof/facts.rs` now owns the ordered facts,
membership/selection indexes, statement priority batches, reasoning contexts,
and incremental freshness indexes. Variable and memory-state reservations stay
with the store because insertion extends them from the new fact's syntax;
explicitly reserved proof names extend that same freshness index. Fresh-name
allocation budgets remain outside the store.

A statement-local store shares the ambient store's variable and memory-state
reservations before extending them with its selected facts. Reserving extra
names prevents capture without making extra propositions available. This
avoids enumerating the variables of an already-retained memory state again.
`statement_local_reservations_share_ambient_memory` grows unrelated memory at
sizes 32, 128, and 512 and bounds the newly collected variables.

`ProofFacts` pairs a store with checked rewritten-load evidence, retaining that
evidence across store successors. Read-only queries delegate to the store.
Mutations construct store successors; `ProofFacts` has no second proposition
collection or reasoning context.

`PureFactList` can be a view of an append-only statement-local store. In that
mode its legacy map,
syntax index, and context cache stay empty. Strict written conjunction queries
use the store's syntax index, separately from the aliases accepted by proof
reasoning. Statement-local construction enables that index; general proof
stores do not build it. A shared store view presents each available proposition
once.
General proof-to-list conversions still use the legacy representation, which
supports occurrence-oriented edits and statement priority order. Retention or
reordering of a local store view materializes the legacy representation
explicitly until those callers migrate.

The overlapping responsibilities before extraction were:

| Current type | Relevant responsibilities | Source |
| --- | --- | --- |
| `PureFactList` | Ordered propositions, exact/conjunct index, cached context, and retained source `ProofFacts`. | `src/surface/pure_fact_list.rs` |
| `ProofFacts` | Ordered propositions, proof selection indexes, variable reservations, and reasoning contexts. | `src/kernel/proof/facts.rs` |
| `PureFactContext` | Assumed facts and maintained reasoning indexes/graphs. | `src/kernel/primitives.rs`, `src/kernel/assumptions.rs` |
| `ExecutionFacts` | Ordered execution evidence and membership indexes. | `src/kernel/execution_facts.rs` |

`PureFactList::from_proof_facts`, `extended_to_proof_facts`, and `proof_facts`
remain the general proof/list migration boundary for stage 4. The ordinary
statement driver already borrows its ambient `ProofFacts` directly; its local
facts are the first store-backed view. Preserve the checked context's lineage,
including
its association with resources; replaying equal propositions into a fresh
context is not a substitute for retaining that context.

## One statement transition

The selected path is an ordinary `step()` through
`check_statement_step_with_policy`, including a store inside a previously
selected C branch. The ambient proof scope and the selected statement's local
scope are distinct stores. Combining them at publication does not make every
ambient fact an explicit premise of the statement theorem.

| Boundary | Operation and authority | Storage behavior |
| --- | --- | --- |
| Focused proof to checked driver | `check_statement_step_with_policy` borrows the ambient `ProofFacts` and its assumptions. | Retains the ambient store and checked context; no enumeration. |
| Select statement-local inputs | The driver selects available case assumptions and observable resource facts, preserving their written order and the checked case context when present. | `PureFactList::for_statement` constructs one local store; its Surface map/index/cache stay empty. These are explicitly selected inputs, not a copy of ambient facts. |
| Advance the frontier | `execute_step_successor_from_frontier_position` clones the local view and calls `execute_step_from_frontier_position_selecting_path`. | Cloning shares persistent storage. Execution state and the caller's ambient reasoning context retain their existing roles. |
| Certify an outcome | `certified_statement_transitions` executes under the selected context; `certified_transitions_from_execution` extends each local store with kernel-produced path facts and checks prerequisites under the existing policy. | Appending updates store indexes and reasoning state. Exact conflict/conjunct queries use the store; execution evidence remains on the certified transition. |
| Publish successor facts | The driver uses `with_statement_facts_retaining_prefix` on the ambient store, then `retain_checked_read_fact` for this statement's effect suffix. | Only the selected local result is enumerated. Ambient facts stay shared; the statement batch preserves priority, the producer's case prefix, and typed read authority. |
| Commit the proof successor | The proof-object driver publishes the returned `CheckedStatementStep` atomically. | The successor owns its store version; unsuccessful or sibling paths retain their own versions. |

The first extraction removes the local Surface map, duplicate syntax index,
and independently cached context on this path. The statement-local result is
still enumerated into its explicit publication batch; this is bounded by the
selected inputs and emitted facts, not the ambient proof history.

A branch assumption enters only its selected branch's store. The branch's
checked case prefix can be shared with statement publication; it must not be
inferred from another branch's equal-looking facts. For a memory write, ambient
facts retain their original memory references. Any transported target and its
certified transport remain producer-issued outputs; publication retains typed
read metadata only from the new effect suffix. Facts and evidence from the
other branch cannot justify that transport or read.

Source: `src/surface/proof/checked_drivers/statement_step.rs`,
`src/surface/proof/cursor_execution.rs`,
`src/surface/proof/execution_planning/transition_certification.rs`, and
`src/surface/proof/proof_object/execution_statements.rs`.

## Migration order

1. **Map one statement transition (complete).** Trace the ambient `ProofFacts`
   and statement-local `PureFactList` through a certified statement transition
   and back into `ProofFacts`.
   Record each consumer's ordering, scope, evidence, and query requirements,
   and each copy, rebuild, or reindex. Include a branch and a transported
   memory fact. Completion: a source-backed operation/ownership map that
   determines the first store interface and focused regressions.
2. **Extract the kernel store from `ProofFacts` (complete).** Move proposition ownership,
   common indexes, and the retained reasoning context into `PureFactStore`.
   Delegate existing operations to it; keep proof-specific evidence and
   metadata outside. Classify variable reservations and specialized indexes
   by whether they are derived from available facts or specific to a proof
   operation. Completion: `ProofFacts` no longer separately owns the migrated
   facts or maintains a second copy of their indexes/context.
3. **Share the store through the selected statement path (complete).** Make its Surface
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

The first implementation milestone covers stages 1 through 3: an ordinary
single-successor statement transition uses a shared `PureFactStore` through
planning and checked proof construction, with its former duplicate Surface
storage removed. Stages 4 through 6 remain: general proof/list adapters,
remaining list edits, and execution publication have not migrated.
