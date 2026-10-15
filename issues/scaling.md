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
   mdtest, example or unit test depended on the older compositions. About
   twenty other `resource_compositions.iter()` sites, in load resolution and
   condition reasoning, still scan the whole set. Indexing the set does not
   help on its own: each step rebuilds its assumptions in a fresh context and
   re-admits the snapshots with no lineage to diff against (tried on branch
   `claude/blissful-cori-zfd8s9`, commit `3513b5d2`).
3. **A call rebuilds what the caller keeps.** `call_kept_ownership` expands
   every kept composite at every call (`expand_composites_for_frame`) to
   list the memory the caller keeps, and `CallKeptRanges::with_residual`
   merges every opened range into the edge's identity. At N = 64 this is
   nearly all of `drop_box`'s growth; the rest of the call path is flat.
   The havoc should be defined by the callee's footprint, with "kept" meaning
   everything else, recorded as the residual and answered per address.

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
must not grow with unrelated facts, aliases or owned objects.
`known_drift_heap_object_stores_and_releases` records the remaining
`heap_objects` drift, the release of cause 3, and fails when it stops, so the
fix updates this issue.

## Acceptance

- Each known cause above is fixed in its representation, with a
  deterministic regression at four or more sizes.
- `known_drift_heap_object_stores_and_releases` (now `drop_box` alone)
  becomes an ordinary no-drift test, and `step-scaling-hunt.py heap_objects` shows every simple
  step's work constant in N, up to logarithmic factors; ownership is still
  checked at every store and release.
- No budget or threshold is raised to get there.
