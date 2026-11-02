# solve misses a mirrored order consequent

Soundness: not soundness. A true claim is refused, depending only on which
way an order fact in an implication's consequent is written.

`solve` closes `x != 0 implies x <= 100 implies result == x` from the
premises `x != 0 implies x > 100` and `x <= 100`: after introducing
`x != 0` the implication gives `x > 100`, which contradicts `x <= 100`. With
the same premise written `x != 0 implies 100 < x` it refuses. The two
consequents are one claim (`condition_polarity_forms` lists both), so the
spelling should not decide the outcome.

## Reproduction

`m.c`:

```c
unsigned int zero(unsigned int x) { return 0; }
```

`m.click`:

```click
verifying "m.c";
uint32 zero(uint32 x) {
    requires x != 0u32 implies 100u32 < x;
    requires x <= 100u32;
    ensures x != 0u32 implies x <= 100u32 implies result == x;
}
```

`click verify m.click` refuses `zero.ensures_0`. Replacing `100u32 < x` with
`x > 100u32` verifies. Reproduced on master at 9a794d88b.

The kernel's constructor-clash rule (`constructor_consequent_instances` in
`src/kernel/proof/facts.rs`) states a refuted order antecedent in the
orientation that closes here; that choice works around this miss and can be
simplified once it is fixed.

## Acceptance criteria

- Both spellings of the premise verify `zero`.
- Regression: the reproduction as an mdtest, with both spellings.
