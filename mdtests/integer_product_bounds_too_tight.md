# A false product range is refused

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem too_tight_product(x: Integer, y: Integer) {
    requires -2 <= x;
    requires x <= 3;
    requires -4 <= y;
    requires y <= 5;
    ensures x * y <= 14 by {
        solve() using { -2 <= x; x <= 3; -4 <= y; y <= 5; };
    }
}
```

```expect
fail: solve
```
