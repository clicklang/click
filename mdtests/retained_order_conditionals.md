# Retained order conditionals preserve branch domains

```click
theorem closed_order_conditionals() {
    ensures (if 9u64 < 8u64 { 9u64 } else { 3u64 }) == 3u64 by { known(); }
    ensures (if 9u64 < 10u64 { 9u64 } else { 3u64 }) == 9u64 by { known(); }
    ensures (if 9i64 < 8i64 { 9i64 } else { 3i64 }) == 3i64 by { known(); }
    ensures (if 9u32 < 8u32 { 9u32 } else { 3u32 }) == 3u32 by { known(); }
    ensures (if 9u64 < 8u64 { 1u64 << 64u64 } else { 3u64 }) == 3u64 by { known(); }
    ensures (if 9u64 < 10u64 { 3u64 } else { 1u64 << 64u64 }) == 3u64 by { known(); }
}

theorem dead_read_needs_no_view(p: int32*) {
    ensures (if 9u64 < 8u64 { p[0] } else { 0 }) == 0 by { normalize(); }
}
theorem closed_pointer_guard(p: int32*, q: int32*) {
    ensures (if 9u64 < 8u64 { p } else { q }) == q by { normalize(); }
}

theorem closed_float_guard() {
    ensures (if 9u64 < 8u64 { float32_from_bits(0x3f800000u32) } else { float32_from_bits(0x40000000u32) }) == float32_from_bits(0x40000000u32) by { normalize(); }
}

```

```expect
pass
```
