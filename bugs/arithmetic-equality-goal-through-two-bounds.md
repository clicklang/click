# `arithmetic` refuses an equality goal that needs two bounds and a substitution

`arithmetic()` proves an Integer linear claim from its listed premises. It
should prove an equality goal whenever the premises entail both directions of
it. It refuses this one, although both directions follow by linear combination:

```click
theorem equality_through_two_bounds(a: Integer, d: Integer) {
    requires a == d;
    requires d <= 2;
    requires 2 <= d;
    ensures a == 2 by arithmetic() using {
        a == d;
        d <= 2;
        2 <= d;
    };
}
```

`click verify` reports "`arithmetic` read the current goal as an Integer linear
claim; no combination of the listed premises proves it". Neighbouring cases
verify:
- `d <= 2; 2 <= d` proves `d == 2`.
- `a == d; d == 2` proves `a == 2`.
- `a == d; d <= 2` proves `a <= 2`.

So proving the equality only fails when it needs the two bounds to be combined
with a substitution. Splitting the step into `have d == 2` and then `a == 2`
works around it (`design/concurrency-probes/mutex_counter.click` does this).

## Regression

Add the theorem above as a passing mdtest. Add a companion that drops `2 <= d`
and expects the same refusal, so the fix does not accept a goal with only one
direction.

## Acceptance

- The theorem above verifies with exactly the listed premises.
- Dropping either bound still fails with the current diagnostic.
- The fix decides an equality goal as two inequalities over the same premise
  set, bounded and deterministic like the existing tactic.
