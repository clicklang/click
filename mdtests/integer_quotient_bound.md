# Positive-divisor scaled quotient bounds

Bounds may be negative or symbolic; truncation is toward zero. Native evaluation guards remain separate.

```click
theorem checked_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate special {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}

theorem checked_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate special {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}

theorem use_scaled_quotient(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    requires n <= bound * d;
    ensures bound <= truncating_quotient(n, d) by { apply(integer_positive_divisor_quotient_lower(n, d, bound)); }
    ensures truncating_quotient(n, d) <= bound by { apply(integer_positive_divisor_quotient_upper(n, d, bound)); }
}

```

```expect
pass
```
