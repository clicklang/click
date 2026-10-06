# Machine-integer quantifiers only support int32

## Violated invariant

The specification language admits machine-integer parameters such as `int64`
and `uint8`, but those same types cannot bind a quantifier. This is a lowering
gap, separate from the pure `witness` dispatch gap: lowering refuses the
existential before the witness runs.

```click
theorem identity(n: int64) {
    ensures exists (x: int64) { x == n } by {
        witness { x: n }
        simp();
    }
}
```

The diagnostic is `only int32 and pointer binders are supported`. Replacing
`int64` with `uint8` gives the same refusal. The restriction is in
`lower_exists_proposition_to_spec` in `src/surface/lowering/annotations.rs`;
its C routes are `SpecProposition::ExistsInt32` and `ExistsPointer`.

## Intended regression and acceptance criteria

- Add passing quantified identity and bounded arithmetic proofs for `int64`
  and `uint8`, with false witness bodies and mismatched witness types refused.
- Preserve the exact integer width and signedness in lowering, instantiation,
  and certificate checking; do not narrow the binders to int32.
- Run the focused quantifier and witness tests and `scripts/check.sh`.
