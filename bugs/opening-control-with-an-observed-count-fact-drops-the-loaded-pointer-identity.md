# Opening a control resource with an observed count fact drops the loaded pointer identity

Soundness: incomplete. The open loses a fact the proof needs; no false
acceptance is known. The regression this guards
(`src/surface/proof/proof_object/authority_control_tests.rs`) was a recorder
that accepted a proof it should not have, so the lost fact is worth checking
for soundness while fixing it.

## Violated invariant

`opening_control_retains_loaded_pointer_facts` opens `control(*p)`, whose body
states `fact *obj == count(reference(obj));`. Opening must introduce the newly
constructed pointer identity (`PointerValueEqual`). With the count fact spelled
by exact observations, `fact to_integer(*obj) == to_integer(count(reference(obj)));`,
which is the same native fact, `begin_open` introduces no
`PointerValueEqual`, and the test's assertion fails, with or without
Integer-default arithmetic. Under Integer-default arithmetic the original
spelling reads as the Integer comparison (a count operand is a quantity), and
the identity is missing the same way.

## Reproduction

In `CONTROL_SOURCE` of
`src/surface/proof/proof_object/authority_control_tests.rs`, replace
`fact *obj == count(reference(obj));` with
`fact to_integer(*obj) == to_integer(count(reference(obj)));` and run
`opening_control_retains_loaded_pointer_facts`.

## Acceptance

- The test passes with the count fact in either spelling, and under
  Integer-default arithmetic with the original spelling.
- `mdtests/shared_heap_population_certification.md` (nightly) still verifies.
