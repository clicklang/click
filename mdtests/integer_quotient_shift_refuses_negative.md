# Quotient shifts require a nonnegative numerator

Truncation towards zero is not translation invariant across zero: with x=-1,
k=1, and d=2 the proposed equality would be 0=1.

```click
theorem false_shift(x: Integer, k: Integer) {
    requires -1 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + 2 * k, 2) == truncating_quotient(x, 2) + k by {
        arithmetic_certificate special {
            premise 0: -1 <= x => -1 <= x;
            premise 1: 0 <= k => 0 <= k;
            integer_quotient_shift bounds [0, 1] => truncating_quotient(x + 2 * k, 2) == truncating_quotient(x, 2) + k;
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 requires quotient(x + d * k, d) == quotient(x, d) + k
```
