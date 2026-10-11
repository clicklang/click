# Algebraic-result matches lose their Integer arm binding

An algebraic-valued pure function must substitute every typed constructor field
into its selected arm. Integer fields currently keep the lowering-time variable
in the body instead of the arm's generated binder (or the concrete field).

Reproduction, rejected by `normalize`:

```click
spec enum Box { Box(Integer) }
function identity(b: Box) -> Box {
    match b { Box::Box(n) => Box::Box(n), }
}
theorem preserves(b: Box, n: Integer) {
    requires b == Box::Box(n);
    ensures identity(b) == Box::Box(n) by {
        unfold(identity(b));
        rewrite(b == Box::Box(n));
        normalize();
    }
}
```

The `SpecAlgebraicExpressionNode::Match` evaluator in `src/kernel/spec.rs`
ignores `AlgebraicValue::Integer` when preparing the arm body. Unlike
`SpecIntegerMatchArm`, `SpecAlgebraicResultMatchArm` carries no
`binding_variables` identities to reconnect the lowered Integer body.
The scalar, pointer, and algebraic versions of this reproduction verify after
algebraic constructor-match reduction; the Integer version still fails.

Acceptance: preserve Integer binder identity for both initially concrete and
initially symbolic scrutinees, including nested matches and shadowing. Add
positive proof fixtures and a negative wrong-payload/capture regression, and
check expansion. Do not work around this by unfolding only after rewriting.
