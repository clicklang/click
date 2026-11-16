# Closed native order comparisons remain provable by checking

```click
theorem unsigned32_true(x: uint32) {
    requires x == 9u32;
    ensures x <= 100u32 by { rewrite(x, 9u32); known(); }
}
theorem unsigned32_false(x: uint32) {
    requires x == 9u32;
    ensures not (x <= 5u32) by { rewrite(x, 9u32); known(); }
}
theorem signed64_true(x: int64) {
    requires x == 9i64;
    ensures x <= 100i64 by { rewrite(x, 9i64); known(); }
}
theorem signed64_false(x: int64) {
    requires x == 9i64;
    ensures not (x <= 5i64) by { rewrite(x, 9i64); known(); }
}
theorem unsigned64_true(x: uint64) {
    requires x == 9u64;
    ensures x <= 100u64 by { rewrite(x, 9u64); known(); }
}
theorem unsigned64_false(x: uint64) {
    requires x == 9u64;
    ensures not (x <= 5u64) by { rewrite(x, 9u64); known(); }
}
```

```expect
pass
```
