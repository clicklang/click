# machine integer quantified range stays scoped

```click
theorem bad(n: int32) {
    requires forall (x: uint8) { x <= 255 };
    ensures n <= 255 by { simp(); }
}
```

```expect
fail: could not establish
```
