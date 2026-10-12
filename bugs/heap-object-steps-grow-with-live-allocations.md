# Calls, stores and frees grow with the live heap objects

Each step over one heap object costs work proportional to how many other
heap objects are live, so a function that creates, fills and releases N
objects is quadratic. Unlike the parameter-object bugs
(`call-step-grows-with-kept-parameter-objects.md`,
`field-store-step-grows-with-owned-parameter-objects.md`), these objects live
in distinct heap blocks, so sharing one block is not the whole cause; the
fixes may share a root.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

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

```sh
python3 scripts/step-scaling-hunt.py heap_objects --sizes 4,64,256
```

At N = 64, `pi = make_box()` charges 1,535 units for the first object and
20,146 for the last; `pi->v = i` 90 and 1,454; `drop_box(pi)` 34,579 for the
first release (63 others live) falling to 4,294 for the last. At N = 256 the
largest step is 135,379 units, mean step time is 129 ms, and the proof
charges 30,743,678 units.

Diagnosis (master `b1523c784`, N = 64): this is not the cell walk. Most of
a `make_box` or `drop_box` call's work is resource expansion of every live
`boxed(pj)` the caller keeps:

- `apply_verified_heap_allocation_delta` expands the whole
  `preserved_caller_resources` (`expand_all_composite_resource_facts_at_state`)
  at every call, re-registering each child's addresses in the equality
  graph (`register_pointer_address`, `MemoryAddresses::update`), only to
  look for allocation effects;
- `call_kept_ownership` → `expand_composites_for_frame` expands them again
  for the frame check.

A constant call needs both to look only at the composites the call's
allocations and retirements can name.

Acceptance: a multi-size regression over `heap_objects` shows each call,
store and release step's work and time constant in the number of other live
objects, up to logarithmic factors; ownership is still checked at every
store and release; no budget or threshold is raised.
