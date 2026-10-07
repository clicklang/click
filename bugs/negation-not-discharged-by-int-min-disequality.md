# `requires x != INT_MIN` does not discharge the overflow of `-x`

## Violated invariant

Unary minus on `int32` is undefined only at `INT_MIN`. A precondition that
excludes that one value discharges the obligation, whichever way it is
spelled. `requires x > -2147483647 - 1` and `requires defined(-x)` both let
`int32 f(int32 x) { return -x; }` verify; the equivalent
`requires x != -2147483647 - 1` is refused with `signed overflow`.

The overflow decider `PureFactContext::decide_from_overflow_facts`
(`src/kernel/assumptions/condition_reasoning/overflow_intervals.rs`, the
`Bitvector32SignedSubtractOverflows` arm that unary minus lowers through)
consults order facts and operand intervals and never the recorded
disequalities, so a disequality that excludes the single overflowing operand
is not seen. The same gap is part of
`int32-symbolic-divisor-refused-as-signed-overflow.md`, where the one
overflowing pair of a division is likewise not excluded by a disequality.

## Reproduction

```c filename=neg.c
int32 f(int32 x) { return -x; }
```

```click
verifying "neg.c";
int32 f(int32 x) {
    requires x != -2147483647 - 1;
    ensures result == -x;
} by { execute(); simp(); }
```

Observed on 2026-10-07:

```text
proof error:
  `f.contract` tactic 0
  `execute()` produced undefined behavior
  signed overflow
  `return -x;`
```

The same contract with `requires x > -2147483647 - 1` verifies, and so does
`requires defined(-x)`. `by auto` makes no difference.

## Intended regression

The reproduction as a positive mdtest beside the `x > INT_MIN` spelling, and
a negative with no `requires` that is still refused.

## Acceptance criteria

- A disequality that excludes the only operand value at which a signed
  `int32` operation overflows discharges that operation's overflow condition;
  this covers unary minus at `INT_MIN` and `INT_MIN / -1` when either operand
  is excluded by name.
- `scripts/check.sh` passes.
