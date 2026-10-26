# Affine reasoning about complete nonlinear Integer values

```click
import click::integer;

theorem reconstruction_bound(n: Integer, q: Integer, d: Integer, r: Integer) {
    requires n == q * d + r;
    requires 0 <= r;
    ensures q * d <= n by { solve() using { n == q * d + r; 0 <= r; }; }
}
theorem quotient_remainder_order(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures truncating_quotient(n, d) * d <= n by {
        apply(integer::truncation_identity(n, d));
        apply(integer::nonnegative_dividend_remainder(n, d));
        solve() using {
            n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
            0 <= truncating_remainder(n, d);
        };
    }
}
theorem distribute(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}
theorem observed_distribution(x: int64, y: int64) {
    requires defined(x + 1i64);
    ensures (to_integer(x + 1i64) + 1) * to_integer(y) == to_integer(x + 1i64) * to_integer(y) + to_integer(y) by {
        apply(integer::multiply_add(to_integer(x + 1i64), 1, to_integer(y)));
    }
}
theorem truncating_distribution(n: Integer, d: Integer) {
    requires d != 0;
    ensures (truncating_quotient(n, d) + 1) * d == truncating_quotient(n, d) * d + d by {
        apply(integer::multiply_add(truncating_quotient(n, d), 1, d));
    }
}
```

```expect
pass
```
