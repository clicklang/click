# Pointer field cells were cached as words

Soundness: incomplete. The recorded defect gave an unchanged pointer field
different names after unfold and after a typed load.

The representation repair retains a complete pointer cell, including
provenance and bounds, and same-source no-write
evidence preserves its read identity. Regressions cover ordinary and cached
read identity, upper-half overwrites, wrong read origins, and pointer runs.
See [Memory DAG](../docs/internals/memory-dag.md) and the
[original report](https://github.com/clicklang/click/blob/d3dbacbb7/bugs/pointer-field-cells-are-cached-as-words-a-pointer-read-cannot-use.md)
for the original reproduction and repair evidence.

The [current rbtree rerun](../roadmap/rbtree-example.md#focused-verification-on-current-master)
records the end-to-end checks on master. The general erase proof currently
stops at a model equality before the descent loop. Acceptance remains
verification of that sidecar at default limits, with the pointer-read
regressions preserved.
