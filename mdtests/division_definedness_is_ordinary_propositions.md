# Signed division and remainder have ordinary domain propositions

The nonzero-divisor check and exclusion of MIN / -1 are separate ordinary
propositions. `defined` exposes their conjunction, in both directions, without
an opaque overflow premise.

```click
theorem division_from_domain(a: int32, b: int32) {
    requires b != 0;
    requires a != -2147483648 or b != -1;
    ensures defined(a / b);
    ensures defined(a % b);
}

theorem division_exposes_domain(a: int32, b: int32) {
    requires defined(a / b);
    ensures b != 0;
    ensures a != -2147483648 or b != -1;
}

theorem wide_division_from_domain(a: int64, b: int64) {
    requires b != 0i64;
    requires a != -9223372036854775808i64 or b != -1i64;
    ensures defined(a / b);
    ensures defined(a % b);
}

theorem wide_remainder_exposes_domain(a: int64, b: int64) {
    requires defined(a % b);
    ensures b != 0i64;
    ensures a != -9223372036854775808i64 or b != -1i64;
}
```

```expect
pass
```
