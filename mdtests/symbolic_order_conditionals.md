# Symbolic order guards retain their comparison family

Checking selects the arm from an explicit guard premise; lowering retains
the conditional even when that premise is available.

```click
theorem selected_int32(y: int32) {
    requires y < 8;
    ensures (if y < 8 { 9 } else { 3 }) <= 100 by {
        close() using { y < 8; };
    }
    ensures not (100 <= (if y < 8 { 9 } else { 3 })) by {
        close() using { y < 8; };
    }
}

theorem selected_uint32(y: uint32) {
    requires y < 8u32;
    ensures (if y < 8u32 { 9u32 } else { 3u32 }) <= 100u32 by {
        close() using { y < 8u32; };
    }
    ensures not (100u32 <= (if y < 8u32 { 9u32 } else { 3u32 })) by {
        close() using { y < 8u32; };
    }
}

theorem selected_int64(y: int64) {
    requires y < 8i64;
    ensures (if y < 8i64 { 9i64 } else { 3i64 }) <= 100i64 by {
        close() using { y < 8i64; };
    }
    ensures not (100i64 <= (if y < 8i64 { 9i64 } else { 3i64 })) by {
        close() using { y < 8i64; };
    }
}

theorem selected_uint64(y: uint64) {
    requires y < 8u64;
    ensures (if y < 8u64 { 9u64 } else { 3u64 }) <= 100u64 by {
        close() using { y < 8u64; };
    }
    ensures not (100u64 <= (if y < 8u64 { 9u64 } else { 3u64 })) by {
        close() using { y < 8u64; };
    }
}

```

```expect
pass
```
