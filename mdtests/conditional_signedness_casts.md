# Conditional operands with signedness casts

```click
theorem uint32_to_int32(flag: Bool, x: int32, w: uint32, y: int32) {
    requires x == (w as int32);
    ensures flag implies (if flag { x } else { 3 }) == (w as int32) by {
        intro();
        rewrite(x, w as int32);
        close() using { flag; };
    }
    ensures ((w as int32) < y) implies (if (w as int32) < y { y } else { 3 }) == y by {
        intro();
        close() using { (w as int32) < y; };
    }
}

theorem int32_to_uint32(flag: Bool, x: uint32, w: int32, y: uint32) {
    requires x == (w as uint32);
    ensures flag implies (if flag { x } else { 3u32 }) == (w as uint32) by {
        intro();
        rewrite(x, w as uint32);
        close() using { flag; };
    }
    ensures ((w as uint32) < y) implies (if (w as uint32) < y { y } else { 3u32 }) == y by {
        intro();
        close() using { (w as uint32) < y; };
    }
}

theorem int64_to_uint64(flag: Bool, x: uint64, w: int64, y: uint64) {
    requires x == (w as uint64);
    ensures flag implies (if flag { x } else { 3u64 }) == (w as uint64) by {
        intro();
        rewrite(x, w as uint64);
        close() using { flag; };
    }
    ensures ((w as uint64) < y) implies (if (w as uint64) < y { y } else { 3u64 }) == y by {
        intro();
        close() using { (w as uint64) < y; };
    }
}

theorem uint64_to_int64(flag: Bool, x: int64, w: uint64, y: int64) {
    requires w <= 9223372036854775807u64;
    requires x == (w as int64);
    ensures flag implies (if flag { x } else { 3i64 }) == (w as int64) by {
        intro();
        rewrite(x, w as int64);
        close() using { flag; };
    }
    ensures ((w as int64) < y) implies (if (w as int64) < y { y } else { 3i64 }) == y by {
        intro();
        close() using { (w as int64) < y; };
    }
}
```

```expect
pass
```
