# `auto` bounds a signed quotient or shift by its operand

A signed quotient by a positive constant truncates toward zero, so its
remainder has the operand's sign and is less than the divisor in size:
`c * (x / c) - (c - 1) <= x <= c * (x / c) + (c - 1)`. An arithmetic right
shift by `k` is the floor of `x / 2^k`, so it has the unsigned form,
`2^k * (x >> k) <= x <= 2^k * (x >> k) + (2^k - 1)`. `auto`'s solver takes
these bounds for every such operation among its facts' and goal's terms,
as it takes an unsigned operation's
(`auto_bounds_an_unsigned_quotient_by_its_operand.md`).

```c filename=auto_bounds_a_signed_quotient_by_its_operand.c
int quarter(int x) { return x / 4; }
int halve(int x) { return x >> 1; }
long eighth(long x) { return x / 8; }
```

```click
verifying "auto_bounds_a_signed_quotient_by_its_operand.c";

int32 quarter(int32 x) {
    ensures to_integer(x) <= 4 * to_integer(result) + 3;
    ensures 4 * to_integer(result) - 3 <= to_integer(x);
} by {
    auto();
}

int32 halve(int32 x) {
    ensures 2 * to_integer(result) <= to_integer(x);
    ensures to_integer(x) <= 2 * to_integer(result) + 1;
} by {
    auto();
}

int64 eighth(int64 x) {
    requires x < 0i64;
    ensures result <= 0i64;
} by {
    auto();
}
```

```expect
pass
```
