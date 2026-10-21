# `extract` takes an implication's consequent whole

Modus ponens in `extract` adds the consequent of an available implication
exactly as written, once its antecedents are available. It does not reach
inside that consequent: a conjunct of it is a second `extract`, after the
consequent is a fact. Requesting `y > 0` directly from `x < y implies
(y > 0 and z == 1)` is refused.

```click
theorem consequent_then_conjunct(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures z == 1 or x == 4 by {
        extract(y > 0 and z == 1);
        extract(z == 1);
        assumption();
    }
}

theorem conjunct_of_a_consequent(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures y > 0 or x == 4 by {
        extract(y > 0);
        assumption();
    }
}
```

```expect
fail: `extract` proposition is not a proper conjunct
```
