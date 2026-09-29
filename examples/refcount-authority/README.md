# Refcount authority migration

This parallel sidecar verifies the original C sources in `../refcount/` under
`resource_semantics: authority`. `reference(obj)` is one logical reference;
`control(obj)` owns the allocation, object memory, population authority, and
the invariant `obj->refs == count(reference(obj))`.

The initializer writes the first stored count while transferring ordinary
object memory. The allocation's creator establishes empty authority and folds
the first reference before packaging `control(obj)`. Retain and nonfinal
release borrow that control and create or consume references under it. The
`amount` helpers exchange one checked symbolic batch with the authority;
their contracts preserve `defined(obj->refs)` for the next caller. Final
release consumes the last reference and control, retires the empty authority,
and frees the allocation.

All seven original C functions, including `refcount_pipeline.c` and its
allocation-failure branch, verify through this additive authority sidecar.
The original C files and legacy sidecar remain unchanged pending migration of
the complete refcount fixture group and negative cases.
