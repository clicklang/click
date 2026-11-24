# Named intro names only a universal

An implication goal introduces its antecedent as a fact, and facts have no
names in Click, so `intro(name) { ... }` is refused there with the form to write.

```click
theorem intro_as_on_implication(n: int32) {
    ensures 0 <= n implies 0 <= n by {
        intro(h) {
            close();
        }
    }
}
```

```expect
fail: use `intro(h) { ... }` for a `forall` goal. To introduce an implication premise, write `intro() { ... }`
```
