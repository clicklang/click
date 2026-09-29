# Refcount authority migration

This parallel sidecar verifies the original C sources in `../refcount/` under
`resource_semantics: authority`. `reference(obj)` is one logical reference;
`control(obj)` owns the allocation, object memory, population authority, and
the invariant `obj->refs == count(reference(obj))`.

The initializer writes the first stored count while transferring ordinary
object memory. The allocation's creator establishes empty authority and folds
the first reference before packaging `control(obj)`. Retain and nonfinal
release borrow that control and create or consume one reference under it. Final
release consumes the last reference and control, retires the empty authority,
and frees the allocation.

This is an additive proof frontier. The symbolic `amount` retain/release
helpers and `refcount_pipeline.c` still use the legacy sidecar until checked
symbolic member quantities can cross authority-mode helper contracts. The
original C files are shared by both sidecars and are unchanged.
