# Affine reasoning about complete nonlinear Integer values

```click
theorem reconstruction_bound(n: Integer, q: Integer, d: Integer, r: Integer) {
    requires n == q * d + r;
    requires 0 <= r;
    ensures q * d <= n by { arithmetic() using { n == q * d + r; 0 <= r; } }
}
theorem quotient_remainder_order(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures truncating_quotient(n, d) * d <= n by {
        apply(integer_truncation_identity(n, d));
        apply(integer_nonnegative_dividend_remainder(n, d));
        arithmetic() using {
            n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
            0 <= truncating_remainder(n, d);
        }
    }
}
theorem distribute(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by { apply(integer_multiply_add(a, b, c)); }
}
theorem observed_distribution(x: int64, y: int64) {
    requires defined(x + 1i64);
    ensures (to_integer(x + 1i64) + 1) * to_integer(y) == to_integer(x + 1i64) * to_integer(y) + to_integer(y) by {
        apply(integer_multiply_add(to_integer(x + 1i64), 1, to_integer(y)));
    }
}
theorem truncating_distribution(n: Integer, d: Integer) {
    requires d != 0;
    ensures (truncating_quotient(n, d) + 1) * d == truncating_quotient(n, d) * d + d by {
        apply(integer_multiply_add(truncating_quotient(n, d), 1, d));
    }
}
```

```expect
pass
```
