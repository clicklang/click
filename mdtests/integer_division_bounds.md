# Checked truncating division bounds

Four explicit operand bounds certify quotient and remainder intervals. The
divisor range excludes zero; signs follow truncation toward zero. This is
mathematical Integer arithmetic, separate from native definedness and casts.

```click
theorem bounded_fee_division(n: Integer, d: Integer) {
    requires -9223372036854775808 <= n;
    requires n <= 9223372036854775807;
    requires 1 <= d;
    requires d != 0;
    requires d <= 2147483647;
    ensures -9223372036854775808 <= truncating_quotient(n, d) by {
        close() using { -9223372036854775808 <= n; n <= 9223372036854775807; 1 <= d; d <= 2147483647; };
    }
    ensures truncating_quotient(n, d) <= 9223372036854775807 by {
        close() using { -9223372036854775808 <= n; n <= 9223372036854775807; 1 <= d; d <= 2147483647; };
    }
    ensures -2147483646 <= truncating_remainder(n, d) by {
        close() using { -9223372036854775808 <= n; n <= 9223372036854775807; 1 <= d; d <= 2147483647; };
    }
    ensures truncating_remainder(n, d) <= 2147483646 by {
        close() using { -9223372036854775808 <= n; n <= 9223372036854775807; 1 <= d; d <= 2147483647; };
    }
}

theorem transport_whole_bound(x: Integer, y: Integer, lower: Integer, upper: Integer) {
    requires x == y;
    requires lower <= x;
    requires x <= upper;
    ensures lower <= y by {
        close() using { x == y; lower <= x; };
    }
    ensures y <= upper by {
        close() using { x == y; x <= upper; };
    }
}

```

```expect
pass
```
