# Arithmetic definedness is one ordinary domain

The complete domain can be introduced and eliminated using ordinary logical
proofs. Range checks use mathematical arithmetic, so they do not evaluate
the machine operation they describe.

```click

theorem add32_domain(a: int32, b: int32) {
    requires to_integer(a) + to_integer(b) <= 2147483647;
    requires to_integer(a) + to_integer(b) >= -2147483648;
    ensures defined(a + b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem add32_bounds(a: int32, b: int32) {
    requires defined(a + b);
    ensures to_integer(a) + to_integer(b) <= 2147483647;
    ensures to_integer(a) + to_integer(b) >= -2147483648;
}

theorem subtract32_domain(a: int32, b: int32) {
    requires to_integer(a) - to_integer(b) <= 2147483647;
    requires to_integer(a) - to_integer(b) >= -2147483648;
    ensures defined(a - b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem subtract32_bounds(a: int32, b: int32) {
    requires defined(a - b);
    ensures to_integer(a) - to_integer(b) <= 2147483647;
    ensures to_integer(a) - to_integer(b) >= -2147483648;
}

theorem multiply32_domain(a: int32, b: int32) {
    requires to_integer(a) * to_integer(b) <= 2147483647;
    requires to_integer(a) * to_integer(b) >= -2147483648;
    ensures defined(a * b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem multiply32_bounds(a: int32, b: int32) {
    requires defined(a * b);
    ensures to_integer(a) * to_integer(b) <= 2147483647;
    ensures to_integer(a) * to_integer(b) >= -2147483648;
}

theorem shifts32(a: int32, n: int32) {
    requires 0 <= n and n < 32;
    requires 0 <= a;
    requires a <= (2147483647 >> (n & 31));
    ensures defined(a << n);
    ensures defined(a >> n);
}
theorem negate32(a: int32) {
    requires a != -2147483648;
    ensures defined(-a);
}

theorem add64_domain(a: int64, b: int64) {
    requires to_integer(a) + to_integer(b) <= 9223372036854775807;
    requires to_integer(a) + to_integer(b) >= -9223372036854775808;
    ensures defined(a + b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem add64_bounds(a: int64, b: int64) {
    requires defined(a + b);
    ensures to_integer(a) + to_integer(b) <= 9223372036854775807;
    ensures to_integer(a) + to_integer(b) >= -9223372036854775808;
}

theorem subtract64_domain(a: int64, b: int64) {
    requires to_integer(a) - to_integer(b) <= 9223372036854775807;
    requires to_integer(a) - to_integer(b) >= -9223372036854775808;
    ensures defined(a - b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem subtract64_bounds(a: int64, b: int64) {
    requires defined(a - b);
    ensures to_integer(a) - to_integer(b) <= 9223372036854775807;
    ensures to_integer(a) - to_integer(b) >= -9223372036854775808;
}

theorem multiply64_domain(a: int64, b: int64) {
    requires to_integer(a) * to_integer(b) <= 9223372036854775807;
    requires to_integer(a) * to_integer(b) >= -9223372036854775808;
    ensures defined(a * b) by {
        both { assumption(); } and { assumption(); }
    }
}
theorem multiply64_bounds(a: int64, b: int64) {
    requires defined(a * b);
    ensures to_integer(a) * to_integer(b) <= 9223372036854775807;
    ensures to_integer(a) * to_integer(b) >= -9223372036854775808;
}

theorem shifts64(a: int64, n: int64) {
    requires 0i64 <= n and n < 64i64;
    requires 0i64 <= a;
    requires a <= (9223372036854775807i64 >> (n & 63i64));
    ensures defined(a << n);
    ensures defined(a >> n);
}
theorem negate64(a: int64) {
    requires a != -9223372036854775808i64;
    ensures defined(-a);
}

```

```expect
pass
```
