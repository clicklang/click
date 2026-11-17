# Bitwise conditional arms retain native comparisons

Checking selects the arm from the explicit flag premise.

```click
theorem bitwise_int32_true(flag: Bool, z: int32) {
    requires flag;
    ensures (if flag { (z & 7) } else { 3 }) == (z & 7) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z | 7) } else { 3 }) == (z | 7) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z ^ 7) } else { 3 }) == (z ^ 7) by {
        normalize() using { flag; };
    }
}

theorem bitwise_int32_false(flag: Bool, z: int32) {
    requires not flag;
    ensures (if flag { 3 } else { (z & 7) }) == (z & 7) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3 } else { (z | 7) }) == (z | 7) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3 } else { (z ^ 7) }) == (z ^ 7) by {
        normalize() using { not flag; };
    }
}

theorem bitwise_uint32_true(flag: Bool, z: uint32) {
    requires flag;
    ensures (if flag { (z & 7u32) } else { 3u32 }) == (z & 7u32) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z | 7u32) } else { 3u32 }) == (z | 7u32) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z ^ 7u32) } else { 3u32 }) == (z ^ 7u32) by {
        normalize() using { flag; };
    }
}

theorem bitwise_uint32_false(flag: Bool, z: uint32) {
    requires not flag;
    ensures (if flag { 3u32 } else { (z & 7u32) }) == (z & 7u32) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3u32 } else { (z | 7u32) }) == (z | 7u32) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3u32 } else { (z ^ 7u32) }) == (z ^ 7u32) by {
        normalize() using { not flag; };
    }
}

theorem bitwise_int64_true(flag: Bool, z: int64) {
    requires flag;
    ensures (if flag { (z & 7i64) } else { 3i64 }) == (z & 7i64) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z | 7i64) } else { 3i64 }) == (z | 7i64) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z ^ 7i64) } else { 3i64 }) == (z ^ 7i64) by {
        normalize() using { flag; };
    }
}

theorem bitwise_int64_false(flag: Bool, z: int64) {
    requires not flag;
    ensures (if flag { 3i64 } else { (z & 7i64) }) == (z & 7i64) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3i64 } else { (z | 7i64) }) == (z | 7i64) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3i64 } else { (z ^ 7i64) }) == (z ^ 7i64) by {
        normalize() using { not flag; };
    }
}

theorem bitwise_uint64_true(flag: Bool, z: uint64) {
    requires flag;
    ensures (if flag { (z & 7u64) } else { 3u64 }) == (z & 7u64) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z | 7u64) } else { 3u64 }) == (z | 7u64) by {
        normalize() using { flag; };
    }
    ensures (if flag { (z ^ 7u64) } else { 3u64 }) == (z ^ 7u64) by {
        normalize() using { flag; };
    }
}

theorem bitwise_uint64_false(flag: Bool, z: uint64) {
    requires not flag;
    ensures (if flag { 3u64 } else { (z & 7u64) }) == (z & 7u64) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3u64 } else { (z | 7u64) }) == (z | 7u64) by {
        normalize() using { not flag; };
    }
    ensures (if flag { 3u64 } else { (z ^ 7u64) }) == (z ^ 7u64) by {
        normalize() using { not flag; };
    }
}

```

```expect
pass
```
