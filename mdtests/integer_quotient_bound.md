# Positive-divisor scaled quotient bounds

Bounds may be negative or symbolic; truncation is toward zero. Native evaluation guards remain separate.

```click
import click::integer;

theorem checked_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        solve() using { bound * d <= n; 1 <= d; };
    }
}

theorem checked_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        solve() using { n <= bound * d; 1 <= d; };
    }
}

theorem use_scaled_quotient(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    requires n <= bound * d;
    ensures bound <= truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_lower(n, d, bound));
    ensures truncating_quotient(n, d) <= bound by apply(integer::positive_divisor_quotient_upper(n, d, bound));
}

```

```expect
pass
```
