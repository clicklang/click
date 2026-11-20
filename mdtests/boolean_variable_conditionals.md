# Boolean variable guards preserve native comparisons

The proof uses a flag premise to select an arm; lowering keeps
the conditional even when that premise is available.

```click
theorem flag_true_int32(flag: Bool) {
    requires flag;
    ensures (if flag { 9 } else { 3 }) <= 100 by {
        have (if flag { 9 } else { 3 }) == 9 by known();
        rewrite((if flag { 9 } else { 3 }), 9);
        known();
    }
    ensures (if not flag { 9 } else { 3 }) == 3 by {
        known();
    }
}

theorem flag_false_int32(flag: Bool) {
    requires not flag;
    ensures (if flag { 9 } else { 3 }) <= 100 by {
        have (if flag { 9 } else { 3 }) == 3 by known();
        rewrite((if flag { 9 } else { 3 }), 3);
        known();
    }
    ensures (if not flag { 9 } else { 3 }) == 9 by {
        known();
    }
}

theorem flag_true_uint32(flag: Bool) {
    requires flag;
    ensures (if flag { 9u32 } else { 3u32 }) <= 100u32 by {
        have (if flag { 9u32 } else { 3u32 }) == 9u32 by known();
        rewrite((if flag { 9u32 } else { 3u32 }), 9u32);
        known();
    }
    ensures (if not flag { 9u32 } else { 3u32 }) == 3u32 by {
        known();
    }
}

theorem flag_false_uint32(flag: Bool) {
    requires not flag;
    ensures (if flag { 9u32 } else { 3u32 }) <= 100u32 by {
        have (if flag { 9u32 } else { 3u32 }) == 3u32 by known();
        rewrite((if flag { 9u32 } else { 3u32 }), 3u32);
        known();
    }
    ensures (if not flag { 9u32 } else { 3u32 }) == 9u32 by {
        known();
    }
}

theorem flag_true_int64(flag: Bool) {
    requires flag;
    ensures (if flag { 9i64 } else { 3i64 }) <= 100i64 by {
        have (if flag { 9i64 } else { 3i64 }) == 9i64 by known();
        rewrite((if flag { 9i64 } else { 3i64 }), 9i64);
        known();
    }
    ensures (if not flag { 9i64 } else { 3i64 }) == 3i64 by {
        known();
    }
}

theorem flag_false_int64(flag: Bool) {
    requires not flag;
    ensures (if flag { 9i64 } else { 3i64 }) <= 100i64 by {
        have (if flag { 9i64 } else { 3i64 }) == 3i64 by known();
        rewrite((if flag { 9i64 } else { 3i64 }), 3i64);
        known();
    }
    ensures (if not flag { 9i64 } else { 3i64 }) == 9i64 by {
        known();
    }
}

theorem flag_true_uint64(flag: Bool) {
    requires flag;
    ensures (if flag { 9u64 } else { 3u64 }) <= 100u64 by {
        have (if flag { 9u64 } else { 3u64 }) == 9u64 by known();
        rewrite((if flag { 9u64 } else { 3u64 }), 9u64);
        known();
    }
    ensures (if not flag { 9u64 } else { 3u64 }) == 3u64 by {
        known();
    }
}

theorem flag_false_uint64(flag: Bool) {
    requires not flag;
    ensures (if flag { 9u64 } else { 3u64 }) <= 100u64 by {
        have (if flag { 9u64 } else { 3u64 }) == 3u64 by known();
        rewrite((if flag { 9u64 } else { 3u64 }), 3u64);
        known();
    }
    ensures (if not flag { 9u64 } else { 3u64 }) == 9u64 by {
        known();
    }
}

```

```expect
pass
```
