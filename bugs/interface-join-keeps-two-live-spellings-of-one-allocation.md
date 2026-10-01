# An interface join keeps two live spellings of one allocation

## Violated invariant

A heap allocation is live at most once, so a second `free` of it must be
refused. `CMemory::with_interface_memory_havoc_preserving_loans` unions the
arms' `live_allocations` keyed by pointer spelling. When one arm records an
allocation live under spelling `p` and the other records the same allocation
under a proven-equal spelling `q`, the joined memory holds two live entries
and no record that they are one allocation. `free_heap_block` then accepts a
free through `p` and a second free through `q`, under assumptions that
include `p == q`.

The unit test
`hunt_investigation_join_carries_two_live_spellings_of_one_allocation` in
`src/kernel/primitives/memory_state.rs` builds exactly this state and asserts
that the second free `is_ok()`. It is a passing test that pins the defect: it
turns red when the defect is fixed.

Whether a C program can reach this memory state through the full verifier is
not established. The test constructs the two arm memories directly; no mdtest
drives a branch whose arms name one allocation by two spellings into a join
and then frees it twice.

## Intended regression

Invert the unit test: after the join, the second free through the equal
spelling is refused (or the join itself keeps one live entry for the
allocation), and rename it out of the `hunt_investigation_` module.

Add a negative mdtest that tries to reach the state from C: a branch whose
arms leave one allocation reachable through two pointer expressions the proof
shows equal, a join, then a `free` through each. It must be refused. If the
surface cannot reach the state, record why in the fixture's prose and keep it
as the end-to-end pin.

## Acceptance criteria

- A join of arms that hold one allocation live under proven-equal spellings
  does not let both spellings be freed.
- The inverted unit test and the negative mdtest pass.
- A branch whose arms hold genuinely different allocations still joins with
  both live, and each can be freed once.
