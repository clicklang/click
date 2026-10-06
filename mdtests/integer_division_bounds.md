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
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= n => -9223372036854775808 <= n;
            premise 1: n <= 9223372036854775807 => n <= 9223372036854775807;
            premise 2: 1 <= d => 1 <= d;
            premise 3: d <= 2147483647 => d <= 2147483647;
            integer_division_bounds bounds [0, 1, 2, 3] => -9223372036854775808 <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
    ensures truncating_quotient(n, d) <= 9223372036854775807 by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= n => -9223372036854775808 <= n;
            premise 1: n <= 9223372036854775807 => n <= 9223372036854775807;
            premise 2: 1 <= d => 1 <= d;
            premise 3: d <= 2147483647 => d <= 2147483647;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(n, d) <= 9223372036854775807;
            conclusion 0;
        }
    }
    ensures -2147483646 <= truncating_remainder(n, d) by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= n => -9223372036854775808 <= n;
            premise 1: n <= 9223372036854775807 => n <= 9223372036854775807;
            premise 2: 1 <= d => 1 <= d;
            premise 3: d <= 2147483647 => d <= 2147483647;
            integer_division_bounds bounds [0, 1, 2, 3] => -2147483646 <= truncating_remainder(n, d);
            conclusion 0;
        }
    }
    ensures truncating_remainder(n, d) <= 2147483646 by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= n => -9223372036854775808 <= n;
            premise 1: n <= 9223372036854775807 => n <= 9223372036854775807;
            premise 2: 1 <= d => 1 <= d;
            premise 3: d <= 2147483647 => d <= 2147483647;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_remainder(n, d) <= 2147483646;
            conclusion 0;
        }
    }
}

theorem transport_whole_bound(x: Integer, y: Integer, lower: Integer, upper: Integer) {
    requires x == y;
    requires lower <= x;
    requires x <= upper;
    ensures lower <= y by {
        arithmetic_certificate special {
            premise 0: x == y => x == y;
            premise 1: lower <= x => lower <= x;
            integer_relation_transport bounds [0, 1] => lower <= y;
            conclusion 0;
        }
    }
    ensures y <= upper by {
        arithmetic_certificate special {
            premise 0: x == y => x == y;
            premise 1: x <= upper => x <= upper;
            integer_relation_transport bounds [0, 1] => y <= upper;
            conclusion 0;
        }
    }
}

```

```expect
pass
```
