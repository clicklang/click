# `normalize() using` refuses an algebraic equality goal it cites

Soundness: not soundness. Nothing false is accepted; a documented valid step
is refused. The goal is exactly the cited premise.

The violated invariant: [Normalization with selected
premises](../docs/reference/tactics/index.md#normalization-with-selected-premises)
decides "each condition in the goal, at any depth outside binders, including
the goal itself", from a cited premise that is "an equality including an
algebraic one, or its `not`", and decides "an equality or disequality in
either orientation". With `xs == ys` cited and available, a goal `xs == ys`,
`ys == xs`, or (citing `not(xs == ys)`) `not(xs == ys)` over `List<T>` should
become `true`. All three are refused. The same citation does decide the
algebraic equality when it is a conditional-expression guard, and the
corresponding `int32` goal `a == b` under `using { a == b; }` verifies.

A suspected cause, from reading `normalize_using_conditions`: a top-level
`Proposition::Equal` between algebraic values is handled as a term rewrite
(`TermRewrite::term`) rather than as a condition, so the cited condition is
never consulted for it.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

theorem t<T>(xs: List<T>, ys: List<T>) {
    requires xs == ys;
    ensures xs == ys by {
        normalize() using { xs == ys; };
    }
}
```

`click verify` prints:

```text
proof error:
  `normalize using` goal did not normalize to true using the listed conditions

tactic@6:
  normalize() using { xs == ys; };
goal: xs == ys
refused by: `normalize` (simple: a refusal within its documented behavior is a bug)
see: click docs normalize
```

Variants that fail with the same message:

- `ensures ys == xs` with the same `using { xs == ys; }`;
- `requires not(xs == ys); ensures not(xs == ys) by { normalize() using { not(xs == ys); }; }`.

Control that verifies: `ensures (if xs == ys { 7 } else { 0 }) == 7` with the
same `using { xs == ys; }`.

## Acceptance criteria

- The reproduction and both variants verify.
- An algebraic equality goal not stated by any cited premise, such as
  `xs == zs` with only `xs == ys` cited and no equality graph path, is still
  refused.
- Regressions keep the source pattern: a top-level algebraic equality goal,
  each orientation, and its `not`, decided by `normalize() using`.
