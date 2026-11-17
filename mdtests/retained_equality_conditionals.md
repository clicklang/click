# Retained wide equality guards keep their branch domains

```click
theorem closed_int64_equality_guards() {
    ensures (if 9i64 == 8i64 { 9i64 } else { 3i64 }) == 3i64 by { normalize(); }
    ensures (if 9i64 == 9i64 { 9i64 } else { 3i64 }) == 9i64 by { normalize(); }
    ensures (if 9i64 != 8i64 { 9i64 } else { 3i64 }) == 9i64 by { normalize(); }
    ensures (if 9i64 != 9i64 { 9i64 } else { 3i64 }) == 3i64 by { normalize(); }
}

theorem closed_uint64_equality_guards() {
    ensures (if 9u64 == 8u64 { 9u64 } else { 3u64 }) == 3u64 by { normalize(); }
    ensures (if 9u64 == 9u64 { 9u64 } else { 3u64 }) == 9u64 by { normalize(); }
    ensures (if 9u64 != 8u64 { 9u64 } else { 3u64 }) == 9u64 by { normalize(); }
    ensures (if 9u64 != 9u64 { 9u64 } else { 3u64 }) == 3u64 by { normalize(); }
}

theorem dead_equality_shift() {
    ensures (if 9u64 == 8u64 { 1u64 << 64u64 } else { 3u64 }) == 3u64 by { normalize(); }
    ensures (if 9u64 != 8u64 { 3u64 } else { 1u64 << 64u64 }) == 3u64 by { normalize(); }
}

theorem dead_equality_read(p: int32*) {
    ensures (if 9u64 == 8u64 { p[0] } else { 0 }) == 0 by { normalize(); }
}

theorem equality_pointer_control(p: int32*, q: int32*) {
    ensures (if 9u64 == 8u64 { p } else { q }) == q by { normalize(); }
}

theorem equality_float_control() {
    ensures (if 9u64 == 8u64 { float32_from_bits(1u32) } else { float32_from_bits(2u32) }) == float32_from_bits(2u32) by { normalize(); }
}
```

```expect
pass
```
