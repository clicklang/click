# Machine bridges use explicit Integer bounds

A machine operation or cast is related to its exact Integer value using the
two stated bounds on that value. A product bound names both operands' ranges.

```click
theorem signed_add(x: int64) {
    requires defined(x + 1i64);
    ensures to_integer(x + 1i64) == to_integer(x) + 1 by {
        close();
    }
}

theorem cast(z: Integer) {
    requires 0 <= z;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        close() using { 0 <= z; z <= 255; };
    }
}

theorem product(a: Integer, b: Integer) {
    requires -2 <= a;
    requires a <= 3;
    requires -4 <= b;
    requires b <= 5;
    ensures -12 <= a * b by {
        close() using { -2 <= a; a <= 3; -4 <= b; b <= 5; };
    }
    ensures a * b <= 15 by {
        close() using { -2 <= a; a <= 3; -4 <= b; b <= 5; };
    }
}
```

```expect
pass
```
