# A conversion after substitution

`(word & 1) == zero_color()` compares a `uint64` with an `int32` call, so
rewriting with it puts `zero_color() as uint64` into the goal. After `unfold`
the operand is the constant `0`. The proof checks the conversion, the
Integer observation, and addition by zero. The wide cases check the
64-bit identities for `x * 1` and `x * 0`.

```c filename=normalize_evaluates_a_substituted_conversion.c
void unused(void) {}
```

```click
verifying "normalize_evaluates_a_substituted_conversion.c";

function zero_color() -> int32 { 0 }

theorem converted_zero(word: uint64, base: uint64) {
    requires to_integer(word) == to_integer(base) + to_integer(word & 1);
    requires (word & 1) == zero_color();
    ensures to_integer(word) == to_integer(base) by {
        rewrite(to_integer(word), to_integer(base) + to_integer(word & 1));
        rewrite((word & 1), zero_color());
        unfold(zero_color());
        known();
    }
}

theorem wide_unit_products(x: uint64, y: int64) {
    ensures x * 1 == x by { known(); }
    ensures 0 * x == 0 by { known(); }
    ensures 1 * y == y by { known(); }
}
```

```expect
pass
```
