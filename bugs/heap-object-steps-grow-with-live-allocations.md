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

Acceptance: a multi-size regression over `heap_objects` shows each call,
store and release step's work and time constant in the number of other live
objects, up to logarithmic factors; ownership is still checked at every
store and release; no budget or threshold is raised.
