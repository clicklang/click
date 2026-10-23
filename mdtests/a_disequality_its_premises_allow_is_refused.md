# a disequality its premises allow is refused

`k <= j` admits `k == j`, so it does not refute the equality a disequality
goal denies, and `arithmetic()` refuses `k != j` from it.

```click
theorem allowed_equality(k: Integer, j: Integer) {
    requires k <= j;
    ensures k != j by { arithmetic() using { k <= j; }; }
}
```

```expect
fail: no combination of the listed premises proves it
```
