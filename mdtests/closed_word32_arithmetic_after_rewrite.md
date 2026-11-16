# Closed 32-bit arithmetic remains checkable after rewriting

```click
theorem signed_operations(x: int32) {
    requires x == 9;
    ensures (x / 3) as int32 <= 5 by { rewrite(x, 9); known(); }
    ensures (x % 3) as int32 <= 5 by { rewrite(x, 9); known(); }
    ensures (x >> 3) as int32 <= 5 by { rewrite(x, 9); known(); }
}

theorem unsigned_operations(x: uint32) {
    requires x == 9u32;
    ensures (x / 3u32) as uint32 <= 5u32 by { rewrite(x, 9u32); known(); }
    ensures (x % 3u32) as uint32 <= 5u32 by { rewrite(x, 9u32); known(); }
    ensures (x >> 3u32) as uint32 <= 5u32 by { rewrite(x, 9u32); known(); }
}
```

```expect
pass
```
