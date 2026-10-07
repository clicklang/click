# by takes one tactic without braces

A one-step proof needs no block: `by T(args);` is `by { T(args); }` for any
tactic, on a claim and on a `have`, including a tactic with a `using` list.

```click
theorem one_step_proofs(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by assumption();
    ensures x + 0 == x + 0 by normalize();
    ensures 0 <= x by {
        have x == x by normalize();
        have 0 <= x by simp() using { 0 <= x; }
        assumption();
    }
}
```

```expect
pass
```
