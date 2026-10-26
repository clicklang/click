# Full-width unsigned subtraction by zero

The neutral operand preserves the complete symbolic `uint64` value, including
its high bits. Rewriting a proven zero remainder uses the same checked identity.

```click
theorem subtract_zero(n: uint64) {
    ensures to_integer(n - 0u64) == to_integer(n) by normalize();
    ensures (n - 0u64) as uint32 as int32 == n as uint32 as int32 by normalize();
}

theorem subtract_zero_after_rewrite(n: uint64) {
    requires n % 4u64 == 0u64;
    ensures to_integer(n - n % 4u64) == to_integer(n) by {
        rewrite(n % 4u64 == 0u64); normalize();
    }
}

theorem subtract_self(n: uint64) {
    ensures to_integer(n - n) == to_integer(0u64) by normalize();
    ensures (n - n) as uint32 as int32 == 0 by normalize();
}

theorem subtract_self_compound(n: uint64) {
    ensures to_integer((n + 1u64) - (n + 1u64)) == to_integer(0u64) by {
        apply(subtract_self(n + 1u64)); assumption();
    }
}

theorem subtract_self_high_bits() {
    ensures to_integer(18446744073709551615u64 - 18446744073709551615u64) == to_integer(0u64) by normalize();
}

theorem subtract_zero_high_bits() {
    ensures to_integer(18446744073709551615u64 - 0u64) == to_integer(18446744073709551615u64) by normalize();
}
```

```expect
pass
```
