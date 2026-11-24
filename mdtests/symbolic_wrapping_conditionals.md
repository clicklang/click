# Conditional operands with two-variable unsigned arithmetic

```click
theorem add_uint32(flag: Bool, x: uint32, z: uint32, w: uint32, y: uint32) {
    requires x == ((z + w) as uint32);
    ensures flag implies (if flag { x } else { 3u32 }) == ((z + w) as uint32) by {
        intro() {
            rewrite(x, (z + w) as uint32);
            close() using { flag; };
        }
    }
    ensures ((z + w) as uint32 < y) implies (if (z + w) as uint32 < y { z } else { 3u32 }) == z by {
        intro() {
            close() using { (z + w) as uint32 < y; };
        }
    }
}

theorem multiply_uint64(flag: Bool, x: uint64, z: uint64, w: uint64, y: uint64) {
    requires x == ((z * w) as uint64);
    ensures flag implies (if flag { x } else { 3u64 }) == ((z * w) as uint64) by {
        intro() {
            rewrite(x, (z * w) as uint64);
            close() using { flag; };
        }
    }
    ensures ((z * w) as uint64 < y) implies (if (z * w) as uint64 < y { z } else { 3u64 }) == z by {
        intro() {
            close() using { (z * w) as uint64 < y; };
        }
    }
}
```

```expect
pass
```
