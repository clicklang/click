# Unsigned conditional operands with literal divisors

```click
theorem divide_uint32(flag: Bool, x: uint32, z: uint32, y: uint32) {
    requires x == (z / 3u32);
    ensures flag implies (if flag { x } else { 3u32 }) == (z / 3u32) by {
        intro();
        rewrite(x, z / 3u32);
        solve() using { flag; };
    }
    ensures ((z / 3u32) < y) implies (if (z / 3u32) < y { z } else { 3u32 }) == z by {
        intro();
        solve() using { (z / 3u32) < y; };
    }
}
theorem remainder_uint32(flag: Bool, x: uint32, z: uint32, y: uint32) {
    requires x == (z % 3u32);
    ensures flag implies (if flag { x } else { 3u32 }) == (z % 3u32) by {
        intro();
        rewrite(x, z % 3u32);
        solve() using { flag; };
    }
    ensures ((z % 3u32) < y) implies (if (z % 3u32) < y { z } else { 3u32 }) == z by {
        intro();
        solve() using { (z % 3u32) < y; };
    }
}
theorem divide_uint64(flag: Bool, x: uint64, z: uint64, y: uint64) {
    requires x == (z / 3u64);
    ensures flag implies (if flag { x } else { 3u64 }) == (z / 3u64) by {
        intro();
        rewrite(x, z / 3u64);
        solve() using { flag; };
    }
    ensures ((z / 3u64) < y) implies (if (z / 3u64) < y { z } else { 3u64 }) == z by {
        intro();
        solve() using { (z / 3u64) < y; };
    }
}
theorem remainder_uint64(flag: Bool, x: uint64, z: uint64, y: uint64) {
    requires x == (z % 3u64);
    ensures flag implies (if flag { x } else { 3u64 }) == (z % 3u64) by {
        intro();
        rewrite(x, z % 3u64);
        solve() using { flag; };
    }
    ensures ((z % 3u64) < y) implies (if (z % 3u64) < y { z } else { 3u64 }) == z by {
        intro();
        solve() using { (z % 3u64) < y; };
    }
}
```

```expect
pass
```
