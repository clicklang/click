# `defined` of a `match` claims its taken arm's root

A `match` has no root operation of its own. Its scrutinee is an operand, and
each arm claims its body's root where its pattern matches, as `if` claims its
taken branch's. A known scrutinee selects one arm's claim; the other arm's
body claims nothing.

```click
spec enum Step {
    Next(int32),
    Stay(int32),
}

theorem arm_claims_its_root(a: int32, b: int32) {
    requires defined(match Step::Next(b) {
        Step::Next(x) => x + a,
        Step::Stay(x) => x,
    });
    ensures to_integer(b) + to_integer(a) <= 2147483647 by close();
}

theorem other_arm_claims_nothing(a: int32, b: int32) {
    requires defined(match Step::Stay(b) {
        Step::Next(x) => x + a,
        Step::Stay(x) => x,
    });
    ensures 1 == 1 by close();
}

theorem symbolic(s: Step, a: int32) {
    requires defined(match s {
        Step::Next(x) => x + a,
        Step::Stay(x) => x,
    });
    ensures 1 == 1 by close();
}
```

```expect
pass
```
