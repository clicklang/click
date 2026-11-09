# A theorem's narrow `let` names C's promoted operation inside a proof step

Soundness: not soundness. Each step is checked against the term it lowers
to, so nothing false is accepted; but one name denotes two different terms
in one theorem, so a step written about the `let` proves a fact about
another value, and a correct proof is refused.

A theorem-level `let n: int8 = v + 1;` is the native `int8` sum (decision
G2) where an `ensures` clause names `n`: its goal prints as
`int8 <=(int8((v+1i8)), u)` or `to_integer(v + 1)`. Inside a `have` in that
clause's proof, the same `n` lowers to C's promoted `int32` sum,
`to_integer(v as int32 + 1)`. The typed `let`'s machine-type position is
lost when the binding is re-read in a proof step.

## Reproduction

```click
theorem goal_native(v: int8) {
    let n: int8 = v + 1;
    ensures to_integer(n) <= 127;
}

theorem have_promoted(v: int8) {
    let n: int8 = v + 1;
    ensures to_integer(n) <= 127 by {
        have to_integer(n) <= 127;
        solve();
    }
}
```

`goal_native` verifies (an `int8` value is at most 127). `have_promoted`
is refused at the `have` with `goal: to_integer(v as int32 + 1) <= 127`,
which is false at `v == 127`. Found while writing
`src/surface/tests/width_uniformity.rs`: an explicit
`integer_operation_identity` certificate for `n` filed
`to_integer(v as int32 + 1) == to_integer(v) + 1`, which does not meet the
native goal.

## Acceptance

- A theorem-level typed `let` lowers to the same term in its clauses and in
  every proof step that names it; `have_promoted` above verifies.
- A regression (an mdtest) holds both theorems above, at `int8` and
  `uint16`.
