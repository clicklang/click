# Bitwise complement in conditional comparisons

```click
theorem complement_arm(flag: Bool, x: uint32, z: uint32) {
    requires x == ~z;
    ensures flag implies (if flag { x } else { 3u32 }) == ~z by {
        intro();
        rewrite(x, ~z);
        normalize() using { flag; };
    }
}

theorem complement_guard(z: uint64, y: uint64) {
    ensures (~z < y) implies (if ~z < y { z } else { 3u64 }) == z by {
        intro();
        normalize() using { ~z < y; };
    }
    ensures (not (~z < y)) implies (if ~z < y { z } else { 3u64 }) == 3u64 by {
        intro();
        normalize() using { not (~z < y); };
    }
}
```

```expect
pass
```
