# Reflexive guards retain comparison and conditional structure

Checking uses reflexivity to select the arm; lowering retains both the guard
and the conditional.

```click
theorem reflexive_int32(y: int32) {
    ensures (if y == y { y } else { 3 }) == y by { normalize(); }
    ensures (if y != y { y } else { 3 }) == 3 by { normalize(); }
    ensures (if y < y { y } else { 3 }) == 3 by { normalize(); }
    ensures (if y <= y { y } else { 3 }) == y by { normalize(); }
    ensures (if y > y { y } else { 3 }) == 3 by { normalize(); }
    ensures (if y >= y { y } else { 3 }) == y by { normalize(); }
}

theorem reflexive_uint32(y: uint32) {
    ensures (if y == y { y } else { 3u32 }) == y by { normalize(); }
    ensures (if y != y { y } else { 3u32 }) == 3u32 by { normalize(); }
    ensures (if y < y { y } else { 3u32 }) == 3u32 by { normalize(); }
    ensures (if y <= y { y } else { 3u32 }) == y by { normalize(); }
    ensures (if y > y { y } else { 3u32 }) == 3u32 by { normalize(); }
    ensures (if y >= y { y } else { 3u32 }) == y by { normalize(); }
}

theorem reflexive_int64(y: int64) {
    ensures (if y == y { y } else { 3i64 }) == y by { normalize(); }
    ensures (if y != y { y } else { 3i64 }) == 3i64 by { normalize(); }
    ensures (if y < y { y } else { 3i64 }) == 3i64 by { normalize(); }
    ensures (if y <= y { y } else { 3i64 }) == y by { normalize(); }
    ensures (if y > y { y } else { 3i64 }) == 3i64 by { normalize(); }
    ensures (if y >= y { y } else { 3i64 }) == y by { normalize(); }
}

theorem reflexive_uint64(y: uint64) {
    ensures (if y == y { y } else { 3u64 }) == y by { normalize(); }
    ensures (if y != y { y } else { 3u64 }) == 3u64 by { normalize(); }
    ensures (if y < y { y } else { 3u64 }) == 3u64 by { normalize(); }
    ensures (if y <= y { y } else { 3u64 }) == y by { normalize(); }
    ensures (if y > y { y } else { 3u64 }) == 3u64 by { normalize(); }
    ensures (if y >= y { y } else { 3u64 }) == y by { normalize(); }
}

theorem dead_reflexive_shift(y: uint64) {
    ensures (if y < y { 1u64 << 64u64 } else { 3u64 }) == 3u64 by { normalize(); }
}

theorem dead_reflexive_read(y: uint64, p: int32*) {
    ensures (if y != y { p[0] } else { 0 }) == 0 by { normalize(); }
}
```

```expect
pass
```
