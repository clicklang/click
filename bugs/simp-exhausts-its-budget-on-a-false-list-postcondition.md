# `simp` exhausts its budget on a false postcondition instead of failing promptly

## Violated invariant

A smart tactic that cannot close a goal fails promptly, with a bounded and actionable report. `AGENTS.md` lists a tactic that crosses its budget without a prompt local failure as a tooling defect.

The final `simp()` of a function whose contract makes a false claim about a list predicate runs to the smart work limit and reports exhaustion:

```
verification budget exhausted inside tactic `simp` in `rb_next_descent.contract` exhausted its deterministic smart work budget after 2000001 units (2000000 limit; statement 10, source tactic 73)
```

It takes about five seconds in a release build. A true claim on the same proof closes in well under one second, and other false claims on it (a wrong tree equation, a wrong null test) fail promptly by naming the `ensures` clause. Because of this, a wrong-position negative for `rb_next` could not be pinned as a prompt regression.

The root cause has not been investigated. The message also repeats itself ("budget exhausted inside tactic ... exhausted its ... budget").

## Reproduction

In `mdtests/rb_next_descent.md`, change the contract clause

```
ensures result != 0 implies
    rb_list_adjacent(rb_inorder(plug(old(c.model), old(t.model))), node, result) == 1;
```

to swap the last two arguments, `result, node`, and run `click verify` on the file. The same happens with `node, node`, and with the clause replaced by `rb_list_starts_with(rb_inorder(plug(old(c.model), old(t.model))), result) == 1`. The unit count is deterministic.

## Intended regression

Reduce to the smallest contract whose final `simp()` has a false goal of the form `predicate(list, a, b) == 1` beside a true fact of the same predicate at other arguments, and pin it as an `expect fail` fixture with a work limit well below the smart budget.

## Acceptance criteria

- The false claim is refused by naming the unproved `ensures` clause, within a small fraction of the smart work budget.
- True claims on the same proof still close; no search heuristic is widened to get there.
- `scripts/check.sh` passes.
