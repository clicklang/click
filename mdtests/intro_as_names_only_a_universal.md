# intro as names only a universal

An implication goal introduces its antecedent as a fact, and facts have no
names in Click, so `intro() as name` is refused there with the form to write.

```click
theorem intro_as_on_implication(n: int32) {
    ensures 0 <= n implies 0 <= n by {
        intro() as h;
        assumption();
    }
}
```

```expect
fail: `intro() as h` names the variable of a `forall` goal; this goal introduces a fact, which has no name, so write `intro();`
```
