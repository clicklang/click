# A one-past-the-end pointer is proved unequal to every other object's start

## Violated invariant

This may be a deliberate provenance-model decision:
`docs/concepts/memory-model.md` says two addresses are equal exactly when
their pointers are equal, and no page states how a one-past-the-end pointer
compares with another object. If the decision stands, the fix is to document
the deviation from C11 6.5.9p6 and the executions it excludes; the claim below
is stated against the C standard.

C11 6.5.9p6: two pointers compare equal if both are null, both point at the
same object, or "one is a pointer to one past the end of one array object and
the other is a pointer to the start of a different array object that happens
to immediately follow the first array object in the address space". The last
case has an unspecified answer: it depends on where the implementation places
the two objects. A verifier may therefore not decide `(a + 2) == b` for two
distinct complete objects `int32 a[2]`, `int32 b[2]`; it must leave the
comparison symbolic (or refuse it) when one operand is a one-past-end pointer.

Click decides it. `apply_c_equal` (`src/kernel/eval/operators.rs`, the
`(CValue::Pointer, CValue::Pointer)` arm around line 4420) builds
`pointer_equality_condition(left, right)` (`operators.rs:4916`), which for
different blocks is `ConditionTerm::pointer_equal`, and the decision procedure
resolves equality of pointers into two distinct live blocks to `false`
regardless of the left offset being exactly the block size. The comparison is
not routed through `apply_same_object_pointer_operation`, so no
`PointerArithmetic` outcome or obligation is produced either. The theorem
`result == 0` (and `result == 1` for `!=`) is thus certified for a value the
C standard leaves to the implementation's layout; gcc is free to place `b`
directly after `a` on the stack, in which case `(a + 2) == b` is 1.

## Reproduction

```c filename=repro.c
int32 f(int32 x) { int32 a[2]; int32 b[2]; a[0] = 1; b[0] = 2; return (a + 2) != b; }
```

```click
verifying "repro.c";

int32 f(int32 x) {
    ensures result == 1;
} by { execute(); simp(); }
```

Observed: `1 selected proof verified` (exit 0). `return (a + 2) == b;` with
`ensures result == 0` also verifies. For contrast, `a < b` on the same
objects is refused as `pointer arithmetic left the pointed-to object`
, so the relational operators already treat cross-object comparison as
undefined; only `==`/`!=` decide the one-past-end case.

## Intended regression

The reproduction above, expected to fail: the equality must stay an open
condition (the proof may not close `result == 1`), or be refused with a
diagnostic naming the one-past-the-end operand. Positive companions that must
keep verifying: `a == b` with `ensures result == 0` (two distinct objects,
neither operand one past the end), `(a + 1) == b` with `ensures result == 0`,
and `(a + 2) == (a + 2)` with `ensures result == 1`.

## Acceptance criteria

- `pointer_equality_condition`, or the resolution that decides
  `ConditionTerm::PointerEqual` across blocks, does not decide `false` when
  either operand's offset may equal its block's size and the other operand's
  offset may be zero (the start of a different object). Either leave the
  condition undecided or produce a documented refusal.
- Null and same-block comparisons are unaffected.
- `docs/concepts/undefined-behavior.md` or the memory-model page states how
  one-past-end pointers compare against other objects.
