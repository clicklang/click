# A smart tactic's search inside a `have` is reported as a control engine bug

Soundness: sound. The refusal is correct in outcome, since the `have` is not
proved, and no false claim verifies; only its classification and advice are
wrong.

The violated invariant: a budget refusal names the budget class of the work
that exhausted it. Here the work is a smart tactic's search, `auto()` closing
a `have` body, which may miss within its bounded budget. The refusal instead
reports the deterministic *control* budget of the enclosing `have` and calls
it "a Click engine bug". A reader who trusts it stops proof work to chase a
verifier defect, when the remedy is the documented one for a smart miss:
replace the `auto()` with an explicit step.

## Reproduction

`a-smart-tactic-search-inside-a-have-is-reported-as-a-control-engine-bug.click`
and its `.c`, from the middle stage of a Linux `string_get_size` proof (the
`.%03u` fraction buffer and its `if (j)` join). At line 268, inside the
`j == 0` arm,

```click
have k == 0u64 by { auto(); }
```

is refused after about 2 s:

```text
verification budget exhausted inside tactic `have` in `s3.contract` exhausted its deterministic control work budget after 2500004 units (2500000 limit; statement 25, source tactic 123)
  ...; a slow control tactic is a Click engine bug
```

Under `CLICK_TIMINGS=1` the attributed work is all `simp` work done by the
nested `auto()`: `simp closure: premise spelling` (about 503,000 units),
`simp premise surface across recorded snapshots` (about 191,000),
`simp premise surface at recorded snapshots` (about 189,000), and
`simp closure: indexed goal equality rewrite` (about 110,000).

Replacing the link with `have k == 0u64 by { arithmetic() using { k < 1u64; }; }`
verifies the file in about 2 s.

Observation, not separately reproduced: the same `auto()` link verified
promptly on a build from `db8e0307`, before PRs #1934 to #1950, so one of them
made this search more expensive. That is a bounded smart miss and not by
itself a defect; the defect is only the classification above.

## Acceptance criteria

- Work a nested smart tactic does is charged to, and reported as, the smart
  budget: the refusal names `auto` (or the `simp` it runs) as a smart tactic
  that may miss, with the smart-tactic advice, not "a slow control tactic is
  a Click engine bug".
- A regression keeps this file's pattern, a smart closer inside a `have` that
  exhausts its budget, and checks the refusal's class.
