# Arithmetic cannot render an observed product after a zero rewrite

## Violated invariant

After a checked Integer rewrite, a smart arithmetic proof must emit a
kernel-checkable source certificate or report a bounded search failure.
Rewriting a u32 observation to zero instead leaves a true constant-product goal
that arithmetic proves internally but cannot print. This was reproduced both
inside a zero-factor multiplication proof and in the independent reduction below
on 2026-10-07.

## Reproduction and intended regression

```click
theorem zero_product(a: uint32, b: uint32) {
    requires to_integer(b) == 0;
    ensures to_integer(a) * to_integer(b) == 0 by {
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
}
```

`click verify` reports that arithmetic proved the goal with a 1-node Integer
certificate, but one step cannot be printed in source form. This reproduction
needs no Rust import, native quotient guard, or new multiplication theorem.
It blocks source-form arithmetic certificates after an otherwise supported
Integer equality rewrite involving native observations.

## Acceptance criteria

- Recover checked source spellings after the rewrite, including native
  observations and products normalized to zero.
- Verify, profile, expand, and independently reverify the reduction without
  proof-only implementation changes or a larger search budget.
- Reject missing zero evidence, a nonzero result, and an altered observed
  operand; retain full unsigned interpretation above the signed sign bit.
- Preserve linear translation work in the explicit source and certificate.
