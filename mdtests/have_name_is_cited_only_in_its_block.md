# A fact name is cited only in its block

`have name: P` names its fact to the end of the block that holds it. Citing
the name after that block, here in the other arm of an `if`, is refused with
the reason rather than read as an unknown variable.

```click
theorem t(x: int32) {
    requires x == 5;
    ensures x == 5 by {
        if x >= 0 {
            have five: x == 5;
            normalize() using { five; };
        } else {
            normalize() using { five; };
        }
    }
}
```

```expect
fail: the fact name `five` is out of scope here: `have five: ...` names its fact only to the end of the block that holds it
```
