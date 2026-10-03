# Pure `witness` rejects machine-integer existentials

## Violated invariant

`witness { name: value }` should instantiate the binder of any existential
goal whose binder type the language supports, in every proof context. In a
pure theorem it accepts only `Integer` and algebraic binders. An `int32`
existential, which a C function's contract or a fixed-state proof witnesses
without trouble, is refused:

```click
theorem split_sum(n: int32) {
    requires 0 <= n and n <= 100;
    ensures exists (a: int32, b: int32) { a + b == n and 0 <= a and 0 <= b } by {
        witness { a: n, b: 0 }
        simp();
    }
}
```

```text
proof error:
  pure `witness` currently requires an Integer existential proposition
```

The same proof over `Integer` binders verifies. The refusal comes from
`apply_fixed_state_witness` in
`src/surface/proof/proof_object/fixed_state_steps.rs`: in a pure context it
dispatches an algebraic binder to `apply_pure_algebraic_witness` and every
other binder to `apply_pure_integer_witness`, which matches only
`Sort::Integer`. Machine-integer binders (`int32`, the other C integer types,
and pointers) have no pure route.

## Intended regression

An mdtest with `split_sum` above that verifies, beside the same theorem over
`int64` and `uint8` binders, a pointer-typed existential if pure theorems
support pointer binders, and a negative case whose witness value does not
satisfy the body.

## Acceptance criteria

- In a pure theorem, `witness` instantiates an existential binder of every
  binder type the pure language supports, through the same checked rule the
  fixed-state route uses for that type.
- A witness value of the wrong type is refused with a diagnostic naming the
  binder and both types.
- The regression's positive cases verify and its negative case fails, and
  `scripts/check.sh` passes.
