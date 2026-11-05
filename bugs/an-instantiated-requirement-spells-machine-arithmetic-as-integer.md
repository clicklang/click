# An instantiated theorem requirement spells machine arithmetic as Integer arithmetic

Soundness: diagnostic-only. The kernel checks the requirement it lowered,
the wrapping comparison, and a fact stating the Integer comparison does not
discharge it. Only the printed instantiation and the suggested `have` are
wrong: they quote a different proposition than the one required.

`apply` of a theorem whose machine-typed parameter receives an arithmetic
argument substitutes the argument into the surface requirement and prints it
with `source_click_proposition` (`src/surface/proof/theorem_application.rs`,
`describe_unavailable_theorem_requirement`). The substituted operand is a
surface `Subtract`, which `printing::machine_arithmetic` deliberately leaves
without a cast barrier (it might be pointer arithmetic), so the machine
comparison `100u64 < (n -_u64 k)` prints as `100u64 < (n - k)`. Reparsed, that
text is a comparison that does arithmetic, which the
[Integer specification arithmetic](../docs/reference/language/index.md#integer-specification-arithmetic)
rule reads as `to_integer(100u64) < to_integer(n) - to_integer(k)`. The
search-miss line then tells the author to write exactly that `have`, which
states a different (here false) fact. `source_click_proposition` promises
"Click source that parses back"; this output does not parse back to the same
proposition.

## Reproduction

```click
theorem big(a: uint64) {
    requires 100u64 < a;
    ensures true by { solve(); }
}
theorem g(n: uint64, k: uint64) {
    requires n == 5u64;
    requires k == 30u64;
    ensures true by {
        apply(big(n - k));
        solve();
    }
}
```

Reports:

```text
requirement 1 `100u64 < (n - k)` instantiates to 100u64 < (n - k)
this is a search miss, not a refusal; ... state it first with `have 100u64 < (n - k) by { ... }`
```

Following the advice, `have 100u64 < (n - k) by { solve(); }` is refused as
`could not establish to_integer(100u64) < (to_integer(n) - to_integer(k))`
(false: it is -25). `have 100u64 < (n - k) as uint64 by { solve(); }` verifies
and discharges the requirement, as does the expansion's own spelling
`to_integer(100u64) < to_integer((n - k))`. With `requires n < 20u64; requires
30u64 <= k;` and `requires a < 20u64`, the Integer fact `have n - k < 20u64`
proves but the requirement stays unavailable while the message quotes the
same text.

## Acceptance criteria

- The instantiation and suggested `have` for a machine-typed parameter bound
  to an arithmetic argument print a spelling that reparses to the required
  proposition, e.g. `100u64 < (n - k) as uint64` (cast the substituted
  argument at its parameter's machine type before printing, or print from the
  lowered requirement with the source spelling).
- A regression keeps the reproduction above and checks that the suggested
  `have`, pasted before the `apply`, verifies.
- Integer-typed parameters and non-arithmetic arguments print unchanged.
