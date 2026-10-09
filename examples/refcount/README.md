# Refcount

This project verifies the lifecycle of a heap object whose stored reference
count agrees with the number of logical `reference(obj)` capabilities.

`control(obj)` owns the allocation, object memory, and
`authority(reference(obj))` once for the whole population. Its fact connects
`obj->refs` to `count(reference(obj))`; each `reference(obj)` is a separate
member without a memory body.

`object_init` initializes storage before the caller establishes the authority
and first reference from that fresh allocation.
`object_retain` increments both the stored count and the logical population.
`object_release_nonfinal` consumes one of at least two references and
decrements both counts. `object_release_final` proves that it holds the final
unit, retires the empty authority, and frees the allocation.

The pipeline exercises allocation failure and the complete successful
lifecycle, including symbolic batches of references across helper calls. The C
functions contain only the runtime implementation; all ownership adaptation
stays in the Click sidecar.
