# `arithmetic` names int32 operations in a uint32 mask goal

Soundness: sound. The refusal is correct in outcome; only its explanation is
wrong, so no false claim verifies.

The violated invariant: a refusal names the fragment and operations the goal
actually contains. Here the goal has one `uint32` operation, a bitwise `&`,
and no `int32` operation, but the refusal says it cannot show that "every
int32 operation in the current goal is defined without overflow". A reader
hunts for an int32 overflow that does not exist.

## Reproduction

```click
theorem masked(units: uint32) {
    requires (units & 1u32) <= 1u32;
    requires (units & 1u32) != 1u32;
    ensures (units & 1u32) < 1u32 by {
        arithmetic() using { (units & 1u32) <= 1u32; (units & 1u32) != 1u32; };
    }
}
```

`click verify` reports:

```text
`arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises
```

The same claim over a plain `uint32` variable, `x <= 1u32; x != 1u32 ⊢ x < 1u32`,
is refused with "exactly the listed premises were insufficient", which names
no operation. Combining a non-strict bound with a disequality into a strict
bound is documented for the signed `int32` family and the 64-bit families
only, so refusing the `uint32` claim is not itself the defect.

Found while proving Linux `string_get_size`, where `units & STRING_UNITS_MASK`
selects the units table.

## Acceptance criteria

- The `masked` refusal no longer mentions int32 operations. It either says
  which fragment it read the goal in and why that fragment does not prove it,
  or matches the plain-variable refusal.
- A regression mdtest holds the `masked` theorem with its expected refusal.
