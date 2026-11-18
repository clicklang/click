# Wrapping arithmetic in native conditional comparisons

```click
theorem add_uint32(flag: Bool, x: uint32, z: uint32, y: uint32) {
    requires x == (z + 1u32);
    ensures flag implies (if flag { x } else { 3u32 }) == (z + 1u32) by {
        intro();
        rewrite(x, z + 1u32);
        normalize() using { flag; };
    }
    ensures ((z + 1u32) < y) implies (if (z + 1u32) < y { z } else { 3u32 }) == z by {
        intro();
        normalize() using { (z + 1u32) < y; };
    }
}
theorem add_wraps_uint32() {
    ensures ((4294967295u32 + 1u32) as uint32) == 0u32 by {
        normalize();
    }
}
theorem subtract_uint32(flag: Bool, x: uint32, z: uint32, y: uint32) {
    requires x == (z - 1u32);
    ensures flag implies (if flag { x } else { 3u32 }) == (z - 1u32) by {
        intro();
        rewrite(x, z - 1u32);
        normalize() using { flag; };
    }
    ensures ((z - 1u32) < y) implies (if (z - 1u32) < y { z } else { 3u32 }) == z by {
        intro();
        normalize() using { (z - 1u32) < y; };
    }
}
theorem subtract_wraps_uint32() {
    ensures ((0u32 - 1u32) as uint32) == 4294967295u32 by {
        normalize();
    }
}
theorem add_uint64(flag: Bool, x: uint64, z: uint64, y: uint64) {
    requires x == (z + 1u64);
    ensures flag implies (if flag { x } else { 3u64 }) == (z + 1u64) by {
        intro();
        rewrite(x, z + 1u64);
        normalize() using { flag; };
    }
    ensures ((z + 1u64) < y) implies (if (z + 1u64) < y { z } else { 3u64 }) == z by {
        intro();
        normalize() using { (z + 1u64) < y; };
    }
}
theorem add_wraps_uint64() {
    ensures ((18446744073709551615u64 + 1u64) as uint64) == 0u64 by {
        normalize();
    }
}
theorem subtract_uint64(flag: Bool, x: uint64, z: uint64, y: uint64) {
    requires x == (z - 1u64);
    ensures flag implies (if flag { x } else { 3u64 }) == (z - 1u64) by {
        intro();
        rewrite(x, z - 1u64);
        normalize() using { flag; };
    }
    ensures ((z - 1u64) < y) implies (if (z - 1u64) < y { z } else { 3u64 }) == z by {
        intro();
        normalize() using { (z - 1u64) < y; };
    }
}
theorem subtract_wraps_uint64() {
    ensures ((0u64 - 1u64) as uint64) == 18446744073709551615u64 by {
        normalize();
    }
}
```

```expect
pass
```
