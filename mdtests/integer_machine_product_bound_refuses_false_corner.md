# Product normalization checks all four corners

The admitted inputs a=3 and b=-4 give -12, below the proposed lower bound.

```click
theorem false_bound(a: Integer, b: Integer) {
    requires -2 <= a;
    requires a <= 3;
    requires -4 <= b;
    requires b <= 5;
    ensures -11 <= a * b by {
        normalize() using { -2 <= a; a <= 3; -4 <= b; b <= 5; };
    }
}
```

```expect
fail: `normalize using` goal did not normalize to true
```
