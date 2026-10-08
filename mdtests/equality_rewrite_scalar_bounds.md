# Exact equality rewriting preserves scalar bounds

Rewriting retains unsigned order, full-width signed values, and mathematical
Integer observations. It uses the cited equality directly.

```c filename=bounds.c
void anchor() {}
```

```click
verifying "bounds.c";
theorem reduced_bound(value: uint32, divisor: uint32) {
 requires value < divisor;
 requires divisor == 65521u32;
 ensures value < 65521u32 by {
  rewrite(65521u32 == divisor);
  assumption();
 }
}
theorem wide_unsigned(x: uint64, y: uint64) {
 requires x == y;
 requires y > 4294967295u64;
 ensures x > 4294967295u64 by { rewrite(x == y); assumption(); }
}
theorem wide_signed(x: int64, y: int64) {
 requires x == y;
 requires y < -2147483648i64;
 ensures x < -2147483648i64 by { rewrite(x == y); assumption(); }
}
theorem observed_bound(x: uint32, y: uint32) {
 requires x == 0u32;
 requires to_integer(y) <= 4294967295;
 ensures to_integer(x) + to_integer(y) <= 4294967295 by { rewrite(x == 0u32); simp(); }
}
```

```expect
pass
```
