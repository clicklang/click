# normalize evaluates a substituted conversion

`(word & 1) == zero_color()` compares a `uint64` with an `int32` call, so
rewriting with it puts `(uint64)zero_color()` into the goal. After `unfold`
the operand is the constant `0`, and `normalize` evaluates the conversion
and `to_integer` of the result, then drops the `+ 0`.

`normalize` also reduces `x * 1` and `x * 0` at 64 bits, as at narrower
widths.

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
        rewrite(to_integer(word) == to_integer(base) + to_integer(word & 1));
        rewrite((word & 1) == zero_color());
        unfold(zero_color());
        normalize();
    }
}

theorem wide_unit_products(x: uint64, y: int64) {
    ensures x * 1 == x by { normalize(); }
    ensures 0 * x == 0 by { normalize(); }
    ensures 1 * y == y by { normalize(); }
}
```

```expect
pass
```
