# A sign cast of a nonnegative quotient is the quotient at the other signedness

Rule C: σ of a 32-bit quotient or remainder is the quotient or remainder at
the other signedness of σ of its operands, when the dividend's `int32`
reading is nonnegative and the divisor's is positive. Both readings of each
operand are then one number, truncating and unsigned division agree on it,
and the result fits both formats. σ stays a node of its own; the rule is
read where a comparison naming σ of the quotient is decided or assumed, so
the path on which the two sides differ is refuted, in each direction and
for `/` and `%`.

```c filename=a_sign_cast_of_a_nonnegative_quotient_is_the_quotient_at_the_other_signedness.c
int signed_quotient_read_unsigned(int x, int y) {
    return (unsigned)(x / y) == (unsigned)x / (unsigned)y;
}

int signed_remainder_read_unsigned(int x, int y) {
    return (unsigned)(x % y) == (unsigned)x % (unsigned)y;
}

int unsigned_quotient_read_signed(unsigned n, unsigned d) {
    return (int)(n / d) == (int)n / (int)d;
}

int unsigned_remainder_read_signed(unsigned n, unsigned d) {
    return (int)(n % d) == (int)n % (int)d;
}
```

```click
verifying "a_sign_cast_of_a_nonnegative_quotient_is_the_quotient_at_the_other_signedness.c";

int signed_quotient_read_unsigned(int32 x, int32 y) {
    requires 0 <= x;
    requires 0 < y;
    ensures result == 1;
}

int signed_remainder_read_unsigned(int32 x, int32 y) {
    requires 0 <= x;
    requires 0 < y;
    ensures result == 1;
}

int unsigned_quotient_read_signed(uint32 n, uint32 d) {
    requires 0 <= n as int32;
    requires 0 < d as int32;
    ensures result == 1;
}

int unsigned_remainder_read_signed(uint32 n, uint32 d) {
    requires 0 <= n as int32;
    requires 0 < d as int32;
    ensures result == 1;
}
```

```expect
pass
```
