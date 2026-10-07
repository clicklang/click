# int32 division by a symbolic divisor is refused as signed overflow

## Violated invariant

The only signed overflow of `int32` division is `INT_MIN / -1`, and an
`execute()` that reports undefined behavior names a path the facts leave
reachable. With `requires y > 0`, or `requires y != 0; requires y != -1`, or
the exact exclusion `requires x != -2147483647 - 1 or y != -1`, that path is
excluded. The int64 twin of the same contract is a passing mdtest
(`mdtests/int64_checked_scalar_arithmetic.md`, `quotient(n, d)` under
`requires d > 0i64`), so a neighbouring case says the shape is supported.

The int32 spelling is refused. `PureFactContext::decide_from_overflow_facts`
(`src/kernel/assumptions/condition_reasoning/overflow_intervals.rs`) decides
`Bitvector64SignedDivideOverflows` from both operands' intervals, around line
335, but its `Bitvector32SignedDivideOverflows` arms, around lines 383 to 405,
handle only a constant `-1` divisor, a constant `INT_MIN` dividend, or a
constant on one side. A symbolic divisor with a positive interval, a dividend
bounded away from `INT_MIN`, and a recorded disequality are never consulted,
so the undefined path survives and `execute()` reports `signed overflow` as
the cause. The diagnostic names a cause the preconditions exclude. Only
`requires defined(x / y)` lets symbolic int32 division through today.

## Reproduction

Follow-up: direct operand exclusions (`x != INT_MIN` or `y != -1`)
now discharge the overflow check, including for remainder. They are covered
by `mdtests/int32_single_overflow_exclusions.md`. The original observations
below predate that fix; interval and disjunctive exclusions, and the requested
operand-pair diagnostic, still need their own regression coverage.

```c filename=div.c
int32 f(int32 x, int32 y) { return x / y; }
```

```click
verifying "div.c";
int32 f(int32 x, int32 y) {
    requires y > 0;
    requires x >= 0;
    ensures result >= 0;
} by { execute(); simp(); }
```

Observed on 2026-10-07:

```text
proof error:
  `f.contract` tactic 0
  `execute()` produced undefined behavior
  signed overflow
  C statement at div.md:4:29
  `return x / y;`
```

The same refusal appears for `requires y != 0; requires x >= 0;`,
`requires y != 0; requires y != -1;`, `requires 0 <= x; requires x <= 100;
requires 1 <= y; requires y <= 100;`, and for the exact exclusion
`requires y != 0; requires x != -2147483647 - 1 or y != -1;`, whether stated
as a `requires` or established by `have` before the step. The `int64`
spelling of the first contract passes `execute()`. A related gap in the same
decider: `requires x != -2147483647 - 1` does not discharge `-x`, while
`requires x > -2147483647 - 1` does.

## Intended regression

The reproduction above as a positive mdtest, plus `requires y != 0; requires
y != -1;` and the exact-exclusion spelling as positives, and `requires y !=
0;` alone as a negative that is still refused and whose diagnostic names
`INT_MIN / -1` rather than a bare `signed overflow`.

## Acceptance criteria

- `Bitvector32SignedDivideOverflows` is decided from operand intervals and
  recorded disequalities the way the 64-bit arm is, so each spelling above
  that excludes `INT_MIN / -1` passes `execute()`.
- The refusal that remains names the one operand pair that overflows.
- `scripts/check.sh` passes.
