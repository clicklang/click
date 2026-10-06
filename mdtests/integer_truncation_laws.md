# Symbolic truncating division laws

These laws relate quotient, remainder and dividend without native overflow or
range assumptions. The divisor and dividend guards remain explicit.

```click
theorem check_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d) by {
        apply(integer_truncation_identity(n, d));
    }
}

theorem check_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d) by {
        apply(integer_positive_divisor_remainder_lower(n, d));
    }
}

theorem check_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1 by {
        apply(integer_positive_divisor_remainder_upper(n, d));
    }
}

theorem check_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d) by {
        apply(integer_nonnegative_dividend_remainder(n, d));
    }
}

theorem check_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0 by {
        apply(integer_nonpositive_dividend_remainder(n, d));
    }
}
```

```expect
pass
```
