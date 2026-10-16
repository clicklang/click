# A fact name is not cited in its own proof

The name of `have name: P by { ... }` begins after its proof, so the proof
cannot cite it; doing so is refused with the reason.

```click
theorem t(x: int32) {
    requires x == 5;
    ensures x == 5 by {
        have five: x == 5 by {
            normalize() using { five; };
        }
        normalize() using { five; };
    }
}
```

```expect
fail: `five` names the fact this `have` is proving, so it cannot be cited inside its own proof; restate the proposition
```
