# A logical cached pointer read omits its current-cell equality

## Violated invariant

A checked proof fact about a cached pointer value must compose with a checked
read of the same cell through an equal address. Retaining the value's original
read definition is correct, but does not replace the equality connecting that
value to the current cell. The rbtree child fold fails at this boundary.

## Diagnosis

At the focused red-propagation fold in `____rb_erase_color`, the proof has
`zid->rb_left == rid` and retains `rb_child_links(zid, rid, parent)` across the
rotation helper and callback. The fold's sibling child nevertheless requires a
different read value. The ordinary trace identifies the known read at
snapshot 26 and the required read at snapshot 32 in the investigation capture.
Snapshot labels are local to that capture, not stable kernel identifiers.

A temporary failure-site probe established the following in the actual
comparison context, without changing the original proof context:

- The current cell's cached scalar names the retained pointer value.
- The retained value is already equal to `rid`.
- The graph already equates the current read at the model address with the
  fold's required read. Address congruence is therefore working here.
- The retained value is not equal in the graph to that current read.
- Adding just this last equality to a cloned context makes
  `resource_arguments_proven_equal` succeed. The original still refuses.

This identifies the missing edge for this comparison. It does not establish
that the remaining fold body, or the rest of the rbtree proof, will pass.

`evaluate_logical_memory_load_paths` can return a cached pointer while recording
its current observation separately. `canonicalized_pointer_value_from_int_cell`
registers its original read definition; the logical path removes generated load
defining facts before returning. In contrast, checked child expression evaluation
retains `observed_pointer_read` in a certified producer binding and publishes
the current-cell equality through `retain_pointer_read_definition` after checking
prerequisites. The logical cached path lacks that evidence handoff.

## Small kernel reproduction

Inside the tests in `src/kernel/eval/memory_loads.rs`, use the existing
`logical_pointer_read` helper and a fresh `VerificationSession`:

1. Create an empty `CMemory`, a symbolic address, and a logical pointer read
   `cached` of that memory at the address. Obtain its
   `typed_pointer_read_variable`.
2. Materialize an `Int32(Variable(variable))` cell at that address in a new
   memory `current`, as a resource's cached load naming does.
3. In a context, assume the address equals a second symbolic address `alias`,
   and `cached` equals a third symbolic pointer `model`.
4. Read `current` logically at the original address. It returns `cached`.
5. Construct `required = Pointer::loaded_value(current, alias)` and register
   its pointer-read definition. Construct `observed` at the original address
   in the same current snapshot.
6. `pointers_known_equal(observed, required)` and
   `pointers_known_equal(cached, model)` succeed, but
   `pointers_known_equal(cached, observed)` and
   `pointers_known_equal(model, required)` fail.
7. As a control, evaluate a nonvolatile C pointer load at the original address
   with `require_owned_expression_loads` and the external-read flag. Retain its
   certified facts with `retain_pointer_read_definition`. Both failed equalities
   now succeed. An isolated clone taken before retention still refuses them.

This reduction was run as a temporary unit test: one test passed, including
the missing-edge assertions and the scoped positive control. The full rbtree
run still exits with the original child-argument refusal. The temporary probes
and test were removed from production source after the investigation.

## Acceptance criteria

- Carry the selected logical read's value/current-cell equation to the checked
  proof context, with its prerequisites and branch scope intact.
- Use the shared checked-read equality mechanism; do not add a fold-only alias
  search or reinterpret a mutable global observation as checked evidence.
- Preserve immutable original read definitions and reject changed-cell,
  unproved-alias, unreadable-cell, volatile, and out-of-scope controls.
- Turn the reduction into a positive regression and verify that the original
  rbtree child comparison advances without changing the pinned C program.
- Keep work proportional to selected reads and relevant equality updates.
  Delete this file when the fix and regression coverage land.
