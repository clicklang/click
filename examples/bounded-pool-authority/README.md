# Bounded Pool Authority Lifecycle

This is the first project-level authority checkpoint for the bounded pool.
The sidecar references the C files in `../bounded-pool` directly; no C source
is copied or changed. It proves initialization, checkout, return,
growth, shrink, transfer, and cleanup, plus the original zero-capacity, two-object, and resize
pipelines.

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

Checkout consumes one available slot and the object's private memory, then
produces a concrete `pool_object(pool, object)` member. Return consumes that
member, restores its private memory unchanged, and produces a slot. Both
helpers borrow the control and preserve its conservation invariant. Their
integer bounds follow from that invariant and the supplied member or slot;
checkout needs no additional counter-bound precondition.

The full two-object pipeline initializes two slots, checks out both objects,
writes their private values while the pool control stays closed, returns the
objects in reverse order, and cleans up. Its contract returns ordinary pool
and object memory, preserves the written values, and proves both populations
are empty. Cleanup selects the two returned slots by its entry-capacity field;
a checked equality relates that field to the caller's numerical batch. This
uses the existing contract and proof syntax.

`pool_shrink` consumes an arbitrary nonnegative owned slot quantity, including
zero, while preserving checked-out members and the capacity invariant. It does
not require ownership of the global population's remaining slots. Ordinary
arithmetic lemmas establish the remaining sum's bounds and conservation;
`int32_equal_of_to_integer` transports the resulting mathematical equality back
to machine values. The unchanged resize pipeline initializes one slot, shrinks
it through a helper call, and retires both empty populations.

`pool_grow` produces an arbitrary nonnegative slot quantity while preserving
checked-out members and all existing slots. Its only arithmetic precondition
is the original C addition's definedness; the control invariant supplies the
bounds for both population growth and invariant restoration. Zero growth has
no member effect. Focused regressions reject capacity overflow and slot
creation without matching authority.

`pool_transfer` borrows the source and destination controls, consumes the
source's concrete object member and one destination slot, and produces the
destination member and one source slot. Its proof updates the original C
counters, preserves the object's private value and both capacities, and restores
both conservation invariants. The supplied member and slot establish safe
counter updates; no extra counter-bound precondition is needed. Integrating the
original transfer pipeline is the next separate checkpoint.
