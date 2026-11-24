# Conditional comparisons with a fixed unsigned left shift

```click
theorem shift_arm(flag: Bool, x: uint32, z: uint32) {
    requires x == (z << 1);
    ensures flag implies (if flag { x } else { 3u32 }) == (z << 1) by {
        intro();
        rewrite(x, z << 1);
        close() using { flag; };
    }
}

theorem shift_guard(z: uint64, y: uint64) {
    ensures ((z << 7) < y) implies (if (z << 7) < y { z } else { 3u64 }) == z by {
        intro();
        close() using { (z << 7) < y; };
    }
    ensures (not ((z << 7) < y)) implies (if (z << 7) < y { z } else { 3u64 }) == 3u64 by {
        intro();
        close() using { not ((z << 7) < y); };
    }
}
```

```expect
pass
```
