# Closed native equality comparisons remain provable by checking

Lowering keeps a comparison of two literals as the comparison it reads,
not the Boolean it evaluates to, so `rewrite` produces `1u64 == 0u64` and
`known()` decides it. The equality holds in the `_true` theorems and fails
in the `_false` ones, at each native format family.

```click
theorem signed32_true(x: int32) {
    requires x == 9;
    ensures x == 9 by { rewrite(x, 9); known(); }
}
theorem signed32_false(x: int32) {
    requires x == 9;
    ensures not (x == 5) by { rewrite(x, 9); known(); }
}
theorem unsigned32_true(x: uint32) {
    requires x == 9u32;
    ensures x == 9u32 by { rewrite(x, 9u32); known(); }
}
theorem unsigned32_false(x: uint32) {
    requires x == 9u32;
    ensures not (x == 5u32) by { rewrite(x, 9u32); known(); }
}
theorem signed64_true(x: int64) {
    requires x == 9i64;
    ensures x == 9i64 by { rewrite(x, 9i64); known(); }
}
theorem signed64_false(x: int64) {
    requires x == 9i64;
    ensures not (x == 5i64) by { rewrite(x, 9i64); known(); }
}
theorem unsigned64_true(x: uint64) {
    requires x == 1u64;
    ensures x == 1u64 by { rewrite(x, 1u64); known(); }
}
theorem unsigned64_false(x: uint64) {
    requires x == 1u64;
    ensures not (x == 0u64) by { rewrite(x, 1u64); known(); }
}
theorem unsigned8_false(x: uint8) {
    requires x == (9 as uint8);
    ensures not (x == (0 as uint8)) by { rewrite(x, 9 as uint8); known(); }
}
```

```expect
pass
```
