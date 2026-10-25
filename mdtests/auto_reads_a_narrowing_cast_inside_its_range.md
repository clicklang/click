# `auto` and `arithmetic` read a narrowing cast inside its range

`sf_cap = size` in Linux's `string_get_size` narrows a `u64` to a `u32`. With
`1u64 <= size` and `size < 1000u64`, the cast keeps the value, so
`1u32 <= sf_cap` holds. The linear solver sees `(uint32)size` as an atom of
its own, bounded only by its type, and cannot connect it to `size`.

`auto` assumes `to_integer((uint32)x) == to_integer(x)` for each cast among
the observations, exactly as it assumes an in-range `+` or `-` identity. When
the refutation cites one, it proves the cast's operand inside the
destination's range by the solver, the identity by `integer_cast_identity`,
and then the goal. `narrow_unsigned` needs it for both bounds, and
`narrow_signed` for an `int` from a `long`.

`arithmetic() using` plans the identity itself from two listed bounds on the
operand, as written or as filed natively (`to_integer(x) <= 4294967295` is
filed as `x <= 4294967295u64`): `narrow_by_arithmetic`.

The operand is spelled from the facts that bound it. A precondition reads at
the function's entry, so `1u64 <= x` spells `to_integer(at(entry, x))`.

```c filename=narrow.c
unsigned narrow_unsigned(unsigned long x) { unsigned y = x; return y; }
int narrow_signed(long x) { int y = x; return y; }
unsigned narrow_by_arithmetic(unsigned long x) { unsigned y = x; return y; }
```

```click
verifying "narrow.c";

uint32 narrow_unsigned(uint64 x) {
    requires 1u64 <= x;
    requires x < 1000u64;
    ensures 1u32 <= result and result <= 999u32;
} by {
    step();
    step();
    have 1u32 <= y by { auto(); }
    have y <= 999u32 by { auto(); }
}

int32 narrow_signed(int64 x) {
    requires -5 <= x;
    requires x <= 5;
    ensures -5 <= result and result <= 5;
} by {
    step();
    step();
    have -5 <= y by { auto(); }
    have y <= 5 by { auto(); }
}

uint32 narrow_by_arithmetic(uint64 x) {
    requires 1u64 <= x;
    requires x < 1000u64;
    ensures 1u32 <= result;
} by {
    step();
    step();
    have 0 <= to_integer(x) by { auto(); }
    have to_integer(x) <= 4294967295 by { auto(); }
    have to_integer((uint32) x) == to_integer(x) by {
        arithmetic() using { 0 <= to_integer(x); to_integer(x) <= 4294967295; }
    }
    have 1u32 <= y by { auto(); }
}
```

```expect
pass
```
