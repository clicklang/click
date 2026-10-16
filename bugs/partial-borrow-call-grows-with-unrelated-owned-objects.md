# A call that borrows part of a range grows with unrelated owned objects

Soundness: not soundness. The verdict is right; the work is not bounded by
the state the call touches.

The verification efficiency contract
(`docs/internals/verification-efficiency.md`) requires a call's work to be
independent of owned objects it does not touch, and
`a_call_ignores_unrelated_owned_objects` in
`src/scaling_tests/surface/tests/step_shape_scaling_tests.rs` checks that for a
call that borrows a caller's whole range. A call that borrows only part of
the caller's range is not flat: beside one unrelated owned `struct box` the
call step costs 1427 work units, beside three 1463, about 18 units per object.
All parameter objects share the external argument block, so a step that
visits that block's owned pieces visits every parameter object.

## Reproduction

The `many_objects` generator of `step_shape_scaling_tests.rs` with the callee
owning only half of `data`:

```c filename=hunt.c
struct box {
    int32 v;
};

int32 caller(int32* data, struct box* b0, struct box* b1, struct box* b2) {
    int32 total;
    b0->v = 0;
    b1->v = 1;
    b2->v = 2;
    touch_half(data);
    total = b0->v + b1->v + b2->v;
    return total;
}
```

```click
verifying "hunt.c";

extern void touch_half(int32* data) {
    owns data[0..2];
}

int32 caller(int32* data, struct box* b0, struct box* b1, struct box* b2) {
    owns data[0..4];
    owns *b0;
    owns *b1;
    owns *b2;
} by {
    step(); step(); step(); step(); step(); step(); step();
}
```

Measured on 2026-10-16 on master `14d830db` plus this branch's fixes, with
`assert_flat_across("rejoin_beside_objects", ..., [1, 3], "touch_half(data);")`:
the `touch_half(data);` step grows from 1427 to 1463 between one and three
objects with the rejoin of the returned piece disabled, and from 1581 to 1617
with it, so the growth is in the partial borrow itself, not the rejoin.

## Acceptance

- `assert_flat_across` holds for this shape at sizes 1 and 3, kept as a
  scaling test beside `a_call_ignores_unrelated_owned_objects`.
- The fix names the step that visited the unrelated objects and replaces it
  with an indexed lookup.
