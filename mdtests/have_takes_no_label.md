# `have` takes no label

A `have` fact has no name. Later steps cite it by restating its proposition,
for example in `using { P; }`, so a label before the proposition is refused
with the spelling to write instead.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        have same: x == x;
        simp() using { x == x; };
    }
}
```

```expect
fail: `have` takes no label: write `have P by { ... };` without `same:`
```
