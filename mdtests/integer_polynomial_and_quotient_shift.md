# Explicit polynomial identities and nonnegative quotient shifts

The polynomial node checks ring identities over mathematical integers. A
quotient stays an opaque atom; it is not treated as division in a field.
The separate quotient-shift rule requires a positive constant divisor and
explicit nonnegative numerator and increment bounds. In particular, the
numerator need not be even. `rewrite` composes the two checked identities.

```click
theorem polynomial_successor(n: Integer) {
    ensures (n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1) by {
        arithmetic_certificate special {
            integer_polynomial_identity bounds [] => (n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1);
            conclusion 0;
        }
    }
}

theorem quotient_increment(x: Integer, k: Integer) {
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + 3 * k, 3) == truncating_quotient(x, 3) + k by {
        arithmetic_certificate special {
            premise 0: 0 <= x => 0 <= x;
            premise 1: 0 <= k => 0 <= k;
            integer_quotient_shift bounds [0, 1] => truncating_quotient(x + 3 * k, 3) == truncating_quotient(x, 3) + k;
            conclusion 0;
        }
    }
}

theorem rewrite_numerator(x: Integer, y: Integer) {
    requires x == y;
    ensures truncating_quotient(x, 2) == truncating_quotient(y, 2) by {
        rewrite(x == y);
        normalize();
    }
}
```

```expect
pass
```
