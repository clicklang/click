# Witness requires an existential goal regardless of the value's type

```click
theorem no_existential() {
    ensures 3 == 3 by {
        witness(3);
    }
}
```

```expect
fail: `witness` requires an existential proposition goal
```
