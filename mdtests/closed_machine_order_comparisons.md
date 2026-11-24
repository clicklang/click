# Closed native order comparisons remain provable by checking

```click
theorem unsigned32_true(x: uint32) {
    requires x == 9u32;
    ensures x <= 100u32 by { rewrite(x, 9u32); close(); }
}
theorem unsigned32_false(x: uint32) {
    requires x == 9u32;
    ensures not (x <= 5u32) by { rewrite(x, 9u32); close(); }
}
theorem signed64_true(x: int64) {
    requires x == 9i64;
    ensures x <= 100i64 by { rewrite(x, 9i64); close(); }
}
theorem signed64_false(x: int64) {
    requires x == 9i64;
    ensures not (x <= 5i64) by { rewrite(x, 9i64); close(); }
}
theorem unsigned64_true(x: uint64) {
    requires x == 9u64;
    ensures x <= 100u64 by { rewrite(x, 9u64); close(); }
}
theorem unsigned64_false(x: uint64) {
    requires x == 9u64;
    ensures not (x <= 5u64) by { rewrite(x, 9u64); close(); }
}
```

```expect
pass
```
