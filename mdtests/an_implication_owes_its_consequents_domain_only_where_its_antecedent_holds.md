# An implication owes its consequent's domain only where its antecedent holds

The right side of `implies` is read only where its left side holds, so its
definedness is owed as `left implies requirement`. The left side itself
establishes that requirement here: `s < 64u64` makes `1u64 << s` defined,
and `x > 0` excludes the one divisor, `-1`, that can overflow `y / x`.

```click
theorem shift(s: uint64) {
    requires s < 64u64 implies (1u64 << s) >= 1u64;
    ensures 1 == 1 by solve();
}

theorem divide(x: int32, y: int32) {
    requires x > 0 implies y / x > 1;
    ensures 1 == 1 by solve();
}
```

```expect
pass
```
