# Bounded Pool Authority Lifecycle

This is the first project-level authority checkpoint for the bounded pool.
The sidecar references the C files in `../bounded-pool` directly; no C source
is copied or changed. It proves `pool_init`, `pool_destroy`, and the existing
`pool_zero_pipeline`. `pool_checkout.c` supplies the object type declaration;
checkout is not a verified claim in this companion yet.

`pool_storage(pool)` owns pool memory and both population authorities.
Initialization takes that resource explicitly, requires both populations to
be empty, and produces `pool_control(pool)` plus the requested quantity of
slots. Its capacity argument is arbitrary and nonnegative. Authority creation
belongs to the caller's allocation lifetime, rather than to initialization of
an external pointer.

`pool_control(pool)` packages pool memory, both authorities, and the capacity
and checkout-count invariants. Cleanup consumes the control and the full
entry-capacity slot batch, proves the private-object population is empty,
retires both authorities, and returns ordinary pool memory. The zero-capacity
pipeline checks this complete lifecycle through ordinary helper contracts.
Before cleanup, its proof briefly exposes and restores the control to establish
slot conservation and private-object emptiness.

Run `click verify examples/bounded-pool-authority/pool_lifecycle.click` from the
repository root. The example gate also verifies the companion automatically.

The other bounded-pool pipelines, including checkout/return, resize, and
transfer, remain in the original project during migration. Focused authority
fixtures already cover several of their prerequisites; integrate them in
separate green checkpoints.
