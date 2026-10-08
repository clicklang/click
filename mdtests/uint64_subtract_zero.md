# Full-width unsigned subtraction by zero

The neutral operand preserves the complete symbolic `uint64` value, including
its high bits. Rewriting a proven zero remainder uses the same checked identity.

```click
theorem subtract_zero(n: uint64) {
    ensures n - 0u64 == n by { normalize(); }
    ensures (int32)(uint32)(n - 0u64) == (int32)(uint32)n by { normalize(); }
}

theorem subtract_zero_after_rewrite(n: uint64) {
    requires n % 4u64 == 0u64;
    ensures n - n % 4u64 == n by {
        rewrite(n % 4u64 == 0u64); normalize();
    }
}

theorem subtract_self(n: uint64) {
    ensures n - n == 0u64 by { normalize(); }
    ensures (int32)(uint32)(n - n) == 0 by { normalize(); }
}

theorem subtract_self_high_bits() {
    ensures 18446744073709551615u64 - 18446744073709551615u64 == 0u64 by { normalize(); }
}

theorem subtract_zero_high_bits() {
    ensures 18446744073709551615u64 - 0u64 == 18446744073709551615u64 by { normalize(); }
}
```

```expect
pass
```
