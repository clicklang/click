# Symbolic equality guards retain native comparison structure

Checking uses the explicit guard premise to select an arm. Lowering retains
the conditional and its enclosing comparison.

```click
theorem selected_int32_equal(y: int32) {
    requires y == 8;
    ensures (if y == 8 { 9 } else { 3 }) <= 100 by {
        close() using { y == 8; };
    }
    ensures not (100 <= (if y == 8 { 9 } else { 3 })) by {
        close() using { y == 8; };
    }
}

theorem selected_int32_unequal(y: int32) {
    requires y != 8;
    ensures (if y != 8 { 9 } else { 3 }) <= 100 by {
        close() using { y != 8; };
    }
    ensures not (100 <= (if y != 8 { 9 } else { 3 })) by {
        close() using { y != 8; };
    }
}

theorem selected_uint32_equal(y: uint32) {
    requires y == 8u32;
    ensures (if y == 8u32 { 9u32 } else { 3u32 }) <= 100u32 by {
        close() using { y == 8u32; };
    }
    ensures not (100u32 <= (if y == 8u32 { 9u32 } else { 3u32 })) by {
        close() using { y == 8u32; };
    }
}

theorem selected_uint32_unequal(y: uint32) {
    requires y != 8u32;
    ensures (if y != 8u32 { 9u32 } else { 3u32 }) <= 100u32 by {
        close() using { y != 8u32; };
    }
    ensures not (100u32 <= (if y != 8u32 { 9u32 } else { 3u32 })) by {
        close() using { y != 8u32; };
    }
}

theorem selected_int64_equal(y: int64) {
    requires y == 8i64;
    ensures (if y == 8i64 { 9i64 } else { 3i64 }) <= 100i64 by {
        close() using { y == 8i64; };
    }
    ensures not (100i64 <= (if y == 8i64 { 9i64 } else { 3i64 })) by {
        close() using { y == 8i64; };
    }
}

theorem selected_int64_unequal(y: int64) {
    requires y != 8i64;
    ensures (if y != 8i64 { 9i64 } else { 3i64 }) <= 100i64 by {
        close() using { y != 8i64; };
    }
    ensures not (100i64 <= (if y != 8i64 { 9i64 } else { 3i64 })) by {
        close() using { y != 8i64; };
    }
}

theorem selected_uint64_equal(y: uint64) {
    requires y == 8u64;
    ensures (if y == 8u64 { 9u64 } else { 3u64 }) <= 100u64 by {
        close() using { y == 8u64; };
    }
    ensures not (100u64 <= (if y == 8u64 { 9u64 } else { 3u64 })) by {
        close() using { y == 8u64; };
    }
}

theorem selected_uint64_unequal(y: uint64) {
    requires y != 8u64;
    ensures (if y != 8u64 { 9u64 } else { 3u64 }) <= 100u64 by {
        close() using { y != 8u64; };
    }
    ensures not (100u64 <= (if y != 8u64 { 9u64 } else { 3u64 })) by {
        close() using { y != 8u64; };
    }
}

```

```expect
pass
```
