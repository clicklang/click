# `arithmetic` cannot use an upper bound written as a symbolic difference

## Violated invariant

The `int32` arithmetic certificate sums listed inequalities with positive
coefficients. From `a <= 1000 - b` and `b >= 1` (with `b <= 1000`, so the
difference is defined), adding the two premises gives `a <= 999`. The
planner refuses this. It equally refuses the equality `a == 1000 - b` and
the sum form `a + b <= 1000` with `b >= 1` and bounds on both atoms. It does
prove the goal `1000 - b <= 999` from `b >= 1; b <= 1000`, after which
`simp` substitutes the equality, so a difference is supported in the goal but
not in a premise. An authority
control that caps a population by a second one (`count(reference(p)) +
count(permit(p)) <= CAP`) hits this when proving that an increment cannot
overflow.

## Reproduction

```c
int f(int a, int b) { return 0; }
```

```click
int32 f(int32 a, int32 b) {
    requires b >= 1;
    requires b <= 1000;
    requires a >= 0;
    requires a <= 1000 - b;
    ensures result == 0;
} by {
    have a <= 999 by { arithmetic() using { a <= 1000 - b; b >= 1; b <= 1000; } }
    step();
    simp();
}
```

Observed on 2026-10-07:

```text
proof error:
  current goal does not follow from exactly the listed arithmetic premises (exactly the listed premises were insufficient)
```

Replacing `a <= 1000 - b` with `a == 1000 - b` in both places is refused the
same way. Listing `a + b <= 1000; a >= 0; a <= 1000; b >= 1; b <= 1000;` with the goal
`a <= 999` or `a < 1000` is refused the same way, and `simp()` does not close
either goal.

## Intended regression

Positive mdtests for `a <= 999` from `a <= 1000 - b` and `b >= 1`, and from
`a + b <= 1000` with both atoms bounded, each closed by one listed
`arithmetic() using { ... }`.

## Acceptance criteria

Both regressions verify, as does the equality form, and a false goal
such as `a <= 998` from the same premises is still refused.
