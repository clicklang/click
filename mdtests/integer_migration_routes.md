# Integer arithmetic routes use ordinary proof construction

Strictness, refutation, integer rounding, type ranges, and native comparison
bridges share the composition emitter.

```click
theorem rounded(x: Integer) {
    requires 2 * x <= 5;
    ensures x <= 2 by { close() using { 2 * x <= 5; }; }
}

theorem native64(x: uint64) {
    requires x <= 5u64;
    ensures 2 * to_integer(x) <= 10 by { close() using { x <= 5u64; }; }
}

theorem native_signed64(x: int64) {
    requires x <= 5i64;
    ensures 2 * to_integer(x) <= 10 by { close() using { x <= 5i64; }; }
}

theorem native_byte(x: int8) {
    requires x <= 5;
    ensures 2 * to_integer(x) <= 10 by { close() using { x <= 5; }; }
}

theorem native_strict(a: uint64, b: uint64, c: uint64) {
    requires a <= b;
    requires b < c;
    ensures a < c by { close() using { a <= b; b < c; }; }
}

theorem upper_endpoint(x: uint64) {
    requires x != 18446744073709551615u64;
    ensures x < 18446744073709551615u64 by {
        close() using { x != 18446744073709551615u64; };
    }
}

theorem quotient_slack(x: int64) {
    ensures 4 * to_integer(x / 4i64) - 3 <= to_integer(x) by { close(); }
    ensures to_integer(x) <= 4 * to_integer(x / 4i64) + 3 by { close(); }
}
```

```expect
pass
```
