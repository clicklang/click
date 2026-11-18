# Signed conditional operands with literal divisors

```click
theorem divide_int32(flag: Bool, x: int32, z: int32, y: int32) {
    requires x == (z / 3);
    ensures flag implies (if flag { x } else { 3 }) == (z / 3) by {
        intro();
        rewrite(x, z / 3);
        normalize() using { flag; };
    }
    ensures ((z / 3) < y) implies (if (z / 3) < y { z } else { 3 }) == z by {
        intro();
        normalize() using { (z / 3) < y; };
    }
}
theorem remainder_int32(flag: Bool, x: int32, z: int32, y: int32) {
    requires x == (z % -7);
    ensures flag implies (if flag { x } else { 3 }) == (z % -7) by {
        intro();
        rewrite(x, z % -7);
        normalize() using { flag; };
    }
    ensures ((z % -7) < y) implies (if (z % -7) < y { z } else { 3 }) == z by {
        intro();
        normalize() using { (z % -7) < y; };
    }
}
theorem divide_int64(flag: Bool, x: int64, z: int64, y: int64) {
    requires x == (z / 3i64);
    ensures flag implies (if flag { x } else { 3i64 }) == (z / 3i64) by {
        intro();
        rewrite(x, z / 3i64);
        normalize() using { flag; };
    }
    ensures ((z / 3i64) < y) implies (if (z / 3i64) < y { z } else { 3i64 }) == z by {
        intro();
        normalize() using { (z / 3i64) < y; };
    }
}
theorem remainder_int64(flag: Bool, x: int64, z: int64, y: int64) {
    requires x == (z % -7i64);
    ensures flag implies (if flag { x } else { 3i64 }) == (z % -7i64) by {
        intro();
        rewrite(x, z % -7i64);
        normalize() using { flag; };
    }
    ensures ((z % -7i64) < y) implies (if (z % -7i64) < y { z } else { 3i64 }) == z by {
        intro();
        normalize() using { (z % -7i64) < y; };
    }
}
```

```expect
pass
```
