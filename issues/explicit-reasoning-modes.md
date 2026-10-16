# Pass reasoning modes explicitly, not through thread-locals

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. Several
thread-local flags change what the trusted kernel derives or admits, and
nothing in a function's signature shows that its answer depends on them.
Memo tables are keyed by hand, so each memo has to remember every flag its
computation reads. One memo already does not (below). A reviewer cannot
tell from a call which mode it runs in.

P1 by user direction (2026-10-16).

## Current state and violated invariant

`src/` has 140 `thread_local!` blocks. About 44 are test-only, and most of
the rest are memos, interners, recursion guards and diagnostic sinks. These
production flags change a kernel or proof answer:

- `ALLOW_SORRY` (`src/kernel/sorry.rs`) makes the kernel admit a goal
  without proof. It is set by `with_allow_sorry` for `--allow-sorry`.
- `EXTENDED_DAG_BRIDGING` and `EXPLICIT_DAG_CHECK`
  (`src/kernel/memory_provenance.rs`) change which load equalities and order
  paths are derived, and widen the DAG walk during certificate validation.
  The comment beside them requires behavior outside the scope to stay
  "byte-identical". `EXPLICIT_DAG_CHECK` is set at seven inline
  replace/restore sites, with no named setter.
- `CONNECTION_VARIABLES`, `COLLECTING_HAVOC_RANGES` and
  `DEFER_CONDITION_SNAPSHOTS` (`src/kernel/reasoning/variable_collection.rs`)
  change which variables are collected, and so which facts the planner
  selects.
- `IMPLICIT_AUTO_DISABLED`
  (`src/surface/proof/proof_object/execution_statements.rs`) turns off the
  implicit `auto` search for `expand --claim` and `audit`.
- Budgets and search depths (`DEADLINES`, `TACTIC_WORK_LIMITS`,
  `RUN_WORK_LIMITS`, `SURFACE_SYNTHESIS_BUDGET`, and depth counters such as
  `LOWER_BOUND_SEARCH_DEPTH` and `DISJUNCTION_SPLIT_DEPTH`) stop searches.
- `*_IN_PROGRESS` cycle guards refuse a nested query, so the answer can
  depend on what is already on the call stack.

On the surface side, `REFUSAL_SPELLING` changes what the source printer
writes (see [one-name-resolver-and-printer.md](one-name-resolver-and-printer.md)),
and the driver-decline flags are covered by
[one-tactic-interpreter.md](one-tactic-interpreter.md).

Some memos key the DAG flags in by hand: `KEPT_RANGE_BASE_EQUALITIES`, the
resolution-query memos, `CONTEXT_INCONSISTENCY_*_MEMO` and the DAG
load-equality memo. `ATOMIC_DERIVATION_MEMO` (`src/kernel/assumptions.rs`)
does not. It is keyed on `(premises_id, for_simp)`, and the derivation it
caches reaches `terms_match` in `order_paths.rs`, which reads
`extended_dag_bridging_active()`. So an answer computed inside a bridging
scope can be served outside it, or the reverse. An instrumented run of the
mdtest corpus and the 54 example projects on 2026-10-16 recorded memo hits in
hundreds of runs, but no hit across a scope boundary. The hazard is latent.
It is not reproduced, so it is not filed in `bugs/`.

`design/proof-object-api.md` already sets the rule for memos: "Memo keys use
semantic proof-state identity". A hidden flag is not part of that identity.

The invariant: a mode that can change a kernel or proof answer is a value in
an explicit context, passed to the code that reads it. That context is part
of the key of every memo whose computation depends on it. Thread-locals
remain only for memos keyed on that explicit state, interners,
instrumentation and diagnostic sinks.

## Intended regression

Add a kernel test that runs the same atomic derivation inside and outside a
bridging scope against one fact context. It must give each scope's own
answer whatever order the two calls run in. Add one regression per migrated
flag that runs the two modes back to back and checks that the second does not
reuse the first one's answer. Keep the scaling suites that assert memo hits
(memos must still hit within one mode).

## Acceptance criteria

- `ALLOW_SORRY`, `EXTENDED_DAG_BRIDGING`, `EXPLICIT_DAG_CHECK`, the
  variable-collection flags and `IMPLICIT_AUTO_DISABLED` are fields of an
  explicit context. The thread-locals are removed.
- Every memo whose computation reads a mode keys on it.
  `ATOMIC_DERIVATION_MEMO` does so, with the regression above.
- Budgets and depth limits are either explicit, or documented as refusing
  without changing a successful answer.
- The `*_IN_PROGRESS` guards are each either shown not to change an answer,
  or replaced by an explicit refusal recorded in the result.
- `docs/internals/` lists the thread-locals that remain and why each cannot
  change an answer.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
