# A call requirement over a grown count is missed and printed without its observation

Soundness: diagnostic only. A true call requirement is refused, as a smart
tactic may refuse, and nothing false is accepted. The defect is that the
refusal prints a goal that reads as a different proposition, so stating the
printed goal does not help, while an explicit `auto` at the same point proves
the real requirement.

A call step's implicit `auto` should prove the callee's requirements whenever
an explicit `have <requirement> by auto();` at the call proves them, and the
refusal's `goal:` should print the requirement it tried, with each inserted
`to_integer` written out (`docs/reference/language/index.md`, "Integer
specification arithmetic": expansions and diagnostics print the inserted
`to_integer`).

`child_retain` requires `count(child_ref(obj)) < 2147483647`, an Integer
comparison of the count. After one retain, the count is the machine sum of
the entry count and one, so the second call's requirement is
`to_integer(old(count(child_ref(obj))) + 1) < 2147483647`, under the
consumed-member guard. The implicit `auto` refuses it and prints:

```text
`step()` is missing prerequisite (precondition clause 1 of `child_retain`)
old(count(child_ref(obj))) >= 1 implies old(count(child_ref(obj))) + 1 < 2147483647
goal: old(count(child_ref(obj))) >= 1 implies old(count(child_ref(obj))) + 1 < 2147483647
refused by: the implicit `auto` that proves this statement's requirements
```

The printed `old(count(...)) + 1` reads as the exact Integer sum, not the
observation of the machine sum. Stating the printed goal with
`have ... by auto();` before the call succeeds, and the step is still
refused with the same text. Stating the callee's requirement itself,
`have count(child_ref(obj)) < 2147483647 by auto();`, before each call makes
every step succeed: `auto` proves the observation through the in-range
operation identity there, and the implicit `auto` does not.

## Reproduction

`git show 43fa3bf6:mdtests/repeated_child_retains_keep_the_entry_count_bound.md`
(the fixture before its migration added the three explicit `have` steps) to
`rc.md`, then from the repository root:

```sh
click verify rc.md
```

The first `step(child_retain(obj), {})` after the first succeeds is refused as
above. `mdtests/repeated_child_retains_keep_the_entry_count_bound.md` now
carries the explicit `have count(child_ref(obj)) < 2147483647 by auto();`
before each later call.

## Acceptance criteria

- The refusal prints the requirement with its `to_integer` observation of
  the machine sum, so the printed goal, stated with `have`, is the goal the
  step needs.
- The implicit `auto` of a call step proves the requirement where an
  explicit `auto` of the callee's requirement at the same point proves it,
  or the refusal names the step that closes it. A regression runs the
  original fixture without the explicit `have` steps.
