# A conjunction reads its right side only where its left side holds

The right side of `and` is read only where the left side is true, as C's
`&&` evaluates it. `s < 64u64` makes `1u64 << s` defined, and `x != 0`
makes `y / x` defined, so each requirement owes nothing for its right side.

```click
theorem shift(s: uint64) {
    requires s < 64u64 and (1u64 << s) >= 1u64;
    ensures 1 == 1 by close();
}

theorem divide(x: int32, y: int32) {
    requires x > 0 and y / x > 1;
    ensures 1 == 1 by close();
}

theorem shift_instance() {
    ensures 1 == 1 by apply(shift(3u64));
}
```

```expect
pass
```
