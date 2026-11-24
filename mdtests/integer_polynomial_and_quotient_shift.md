# Explicit polynomial identities and nonnegative quotient shifts

The polynomial node checks ring identities over mathematical integers. A
quotient stays an opaque atom; it is not treated as division in a field.
The separate quotient-shift rule requires a positive constant divisor and
explicit nonnegative numerator and increment bounds. In particular, the
numerator need not be even. `rewrite` composes the two checked identities.

```click
theorem polynomial_successor(n: Integer) {
    ensures (n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1) by {
        close() using {  };
    }
}

theorem quotient_increment(x: Integer, k: Integer) {
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + 3 * k, 3) == truncating_quotient(x, 3) + k by {
        close() using { 0 <= x; 0 <= k; };
    }
}

theorem rewrite_numerator(x: Integer, y: Integer) {
    requires x == y;
    ensures truncating_quotient(x, 2) == truncating_quotient(y, 2) by {
        rewrite(x, y);
        close();
    }
}
```

```expect
pass
```
