# Scaling

Priority: P1.

Soundness: not soundness. This is verifier performance. Every derivation the
steps below perform is kernel-checked today; the problem is that their work
grows with state the step does not touch, so a function with N objects costs
O(N²) to verify. It looks fine at small N and then exhausts budgets.

## Goal

Stamp out every quadratic scaling problem we can find in simple checking.
The contract is in [Verification Efficiency](../docs/internals/verification-efficiency.md):
a simple step's work is bounded by its selected operation, its explicit
inputs, indexed lookups and the proof-state delta, up to logarithmic factors.
A step that scans the whole state, re-derives something from the whole state,
or walks a collection that grows with the proof's history violates it, even
when each scan is cheap.

Fix the underlying representation rather than adding a cache or a skip in
front of a scan that stays linear. A fix is done when a deterministic
regression over several sizes shows the step flat.

## Reproduction

`scripts/step-scaling-hunt.py` generates one C function per shape and size,
with one explicit `step()` per statement, and prints each step's work.

```sh
cargo build --profile profiling --bin click
python3 scripts/step-scaling-hunt.py heap_objects --sizes 4,16,64,256
```

`heap_objects` creates, fills and releases N heap objects:

```c
int32 caller() {
    struct box* p0; ... struct box* pN;
    p0 = make_box(); p0->v = 0;      /* extern: produces boxed(result) */
    ...
    drop_box(p0); ...                /* extern: consumes boxed(p) */
    return 0;
}
```

with `resource boxed(p: struct box*) { owns *p; }`, each object unfolded for
its store and folded again.

On master `a826da1c` at N = 64: `pi = make_box()` is flat at 1,586 units;
`pi->v = i` grows from 1,049 to 1,977; `drop_box(pi)` charges 14,984 for the
first release (63 others live) falling to 1,400 for the last. The whole
proof charges 695,291 units at N = 64 and 13,933,163 at N = 256, with a
largest step of 69,033.

## Known causes

Each is the same pattern: a step recomputes something from the whole state
instead of from what the step changed.

1. **Fixed: a store through an unresolved pointer visited every cached
   cell**, including the slot of every earlier local, which no pointer value
   can reach. The cell store now keeps the pointer-reachable cell keys
   (`CellStore::pointer_reachable_cells`), caught up by diffing, and a store
   through a `Symbolic` pointer visits only those. `heap_objects` stores now
   cost 135 units at every position at N = 64.
2. **Composition evidence is a list that only grows.** Every step states
   about four snapshots of the whole resource context as
   `Proposition::CResourceComposition` facts. Stores no longer read them:
   the write path states the writer's current composition as the store owner
   (`PureFactContext::with_store_owner`), and `owned_store_footprint` and
   `owned_composition_store_separated_evidence` read it alone. That removed
   25 of the 29 units per earlier object a `heap_objects` store cost (cause 1
   was the rest), and no
   mdtest, example or unit test depended on the older compositions. Without
   a store owner, ownership separation and the same-block separation search
   now read only the compositions listed under the two objects' members
   (`CompositionMemberIndex`), each listed by what it holds beyond an
   earlier admitted composition; that held `heap_objects`' `unfold` tactics,
   which grew about 27 units per earlier object, flat. The set itself is a
   persistent set, so stating a composition no longer copies it. About
   twenty other `resource_compositions.iter()` sites, in load resolution and
   condition reasoning, still scan the whole set; each needs the same
   argument for which listed compositions can answer it.
3. **A call rebuilds what the caller keeps.** `call_kept_ownership` expanded
   every kept composite at every call to list the memory the caller keeps.
   Fixed for composites whose definition is argument-direct, such as
   `boxed`: the call opens none of them, and the recorded kept memory opens
   only the composites a question's address can name
   (`CallKeptRanges::range_holding`). `heap_objects` now costs 1,401 units per
   `drop_box` at every position at N = 64, and the whole proof 204,585 units
   (was 695,291). Still per call: residual instances and composites whose
   bodies read memory, a condition or a witness are opened at every call, so
   a function holding many of those still pays for each.
4. **Evidence checking re-validated each step.** A statement theorem listed
   every fact of the context it executed under as a premise, and recording
   it looked each one up again in that same context, and built a set of the
   whole retained history for any premise it missed, uncharged. Fixed in
   part: a statement theorem lists only its own path facts and obligations
   (`statement_theorems_do_not_list_the_context_they_executed_under`), and
   recording a step checks the frontier and running state but walks no
   premises. Memory snapshots and resource contexts also order by a cached
   content hash first, so the lookups that remain no longer walk shared
   entries (`ordering_snapshots_of_one_path_does_not_walk_their_shared_entries`).
   Together, on `heap_objects`: 6.28 to 3.75 billion instructions at
   N = 64, and a mean step of 18.7 to 6.4 ms at N = 256. Still open, under
   the rule in `AGENTS.md` (construct valid proofs; never produce-then-check):
   a step still runs its executor up to three times (a probe before
   obligations, and a call before its `return`), instance, observation and
   population rewrites still re-check their producer's result, joins re-walk
   their arms, and condition and function-level theorems still list their
   contexts. A plain composite `fold` or `unfold` is recorded from its
   producer's result without re-expanding or comparing (2.84 billion
   instructions at N = 64; fold work at N = 256 137,981 to 22,782).
5. **Fixed: satisfying a composite checked every held one of its shape.**
   `ResourceContext::satisfies_fact` tried entailment against every held
   `boxed(..)` when the required pointer was spelled differently, so each
   `heap_objects` fold cost 3 units per live object. It now reads the held
   composites whose pointer is related to the required one
   (`direct_match_candidates_for`), and folds are flat.
6. **A load through an unresolved pointer keeps every cell it may alias.**
   `canonical_memory_for_pointer_load` is assumption-free, and a `Symbolic`
   block's alias candidates narrow nothing, so the canonical memory of a
   load through one heap object keeps every earlier object's cell and every
   local's slot: each `heap_objects` unfold still grows 3 units per earlier
   object. The slots are unreachable by any pointer value, as cause 1 used
   for stores; the other objects' cells need ownership, which
   canonicalization does not consult.

Related scaling bugs stay in `bugs/` until fixed:
[sequential-loop-clause-grows-with-earlier-loops.md](../bugs/sequential-loop-clause-grows-with-earlier-loops.md).

## Scaling tests

The deterministic multi-size work regressions live in `src/scaling_tests/`,
mirroring `src/`, each included into a `scaling_tests` module of the module it
measures; `cargo nextest run --lib -E 'test(/scaling_tests/)'` runs them all
(`docs/internals/testing.md`, "Scaling tests"). Most measure one kernel
operation beside unrelated state built in advance, and such tests pass while
`heap_objects` grows, because its extra state comes from the proof itself.
End-to-end, `src/scaling_tests/surface/tests/step_shape_scaling_tests.rs`
runs the `scripts/step-scaling-hunt.py` shapes in the gate: a step repeated at
several positions must not drift with the statements before it, and a call
must not grow with unrelated facts, aliases or owned objects; `unfold` and
`fold` tactics are held to the same no-drift rule as steps. Step work does not
capture the uncharged costs of cause 4; the hunt script's mean step time does.
`heap_object_stores_and_releases_cost_the_same_at_every_position` holds
`heap_objects` flat; `known_drift_sequential_loop_clauses` records the loop
bug's drift and fails when it stops.

## Acceptance

- Each remaining cause above is fixed in its representation, with a
  deterministic regression at four or more sizes: the composition scans
  outside stores and separation (cause 2), calls beside held instances or
  composites whose bodies read memory, a condition or a witness (cause 3),
  and evidence checking's premise walk and memory comparisons (cause 4),
  charged once linear work is gone.
- `step-scaling-hunt.py` shows every simple step of every shape constant in
  N, up to logarithmic factors and work proportional to the step's own
  effect (as the final `return` ending N locals in `heap_objects` is).
- No budget or threshold is raised to get there.
