# Implication consequents and their conjuncts are ordinary facts

`have` can establish a whole consequent or select a conjunct from it.

```click
theorem consequent_then_conjunct(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures z == 1 or x == 4 by {
        have y > 0 and z == 1;
        have z == 1;
        known();
    }
}

theorem conjunct_of_a_consequent(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures y > 0 or x == 4 by {
        have y > 0;
        known();
    }
}
```

```expect
pass
```
