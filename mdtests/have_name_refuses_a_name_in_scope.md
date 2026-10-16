# `have name: P` refuses a name already in scope

A fact name must not hide another name: a parameter, a binding, or an earlier
fact name in the same block. Reusing one is refused with the reason, so a
later citation of the name cannot be read two ways.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        have x: x == x;
        normalize();
    }
}
```

```expect
fail: `have x: ...` names a fact `x`, but `x` already names something in scope; choose another name
```
