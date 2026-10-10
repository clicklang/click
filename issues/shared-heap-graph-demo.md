# P1: Shared heap graph and resource invariants

## Goal

A child object shared by independently allocated parents is verified with
ordinary population resources. The child is freed exactly once, at its last
reference. This must hold for both a sequential program and a thread-safe
reference count under the modeled pthread runtime. The semantics are in
[Resource invariants, counting, and synchronization](../docs/internals/resource-invariants.md).

The sequential probe
[`design/shared-heap-probes/shared_parent.c`](../design/shared-heap-probes/shared_parent.c)
and the mutex-protected
[`examples/shared-refcount/`](../examples/shared-refcount/README.md) verify,
expand, and audit. The `shared_heap_*` and `refcount_*` mdtests refuse:

- a double release;
- a premature free;
- a read after the final release;
- a duplicate reference;
- a dropped reference without a counter update;
- an unlocked counter update;
- a releaser that frees the shared object.

Keep both C sources frozen.

## Remaining work

Population work must not grow faster than linearly with unrelated live graph
resources. A retain amid unrelated live children now scales near-linearly
through 16 children (`a_retain_ignores_unrelated_live_children`). Beyond 32
owned pointer parameters, per-clause function-exit work still grows faster
than linearly
([bug](../bugs/owning-many-pointer-parameters-is-superlinear.md)).

## Regression

The bug's scaling tests pass `assert_near_linear_scaling` through 64.

## Acceptance

- The bug above is fixed with its regression in the gate.
- The frozen probe and the shared refcount example still verify, expand, and
  audit, and `scripts/check.sh` passes.
- Then delete this issue and its list entry.
