# Rewriting an unsigned shift preserves its high bit

The bitvector shift denotes the resulting bits. C signed-overflow checks
remain separate from substitution and must not erase an unsigned result.

```c filename=unsigned_shift_rewrite_preserves_high_bit.c
unsigned shift(unsigned value, unsigned long count) {
    return value << count;
}
```

```click
verifying "unsigned_shift_rewrite_preserves_high_bit.c";
uint32 shift(uint32 value, uint64 count) {
    requires value == 1u32;
    requires count == 31u64;
    ensures result == 2147483648u32;
} by {
    execute();
    rewrite(count == 31u64);
    rewrite(value == 1u32);
    normalize();
}
```

```expect
pass
```
