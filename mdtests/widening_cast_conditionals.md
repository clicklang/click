# Widening casts in conditional arms preserve source signedness

```click
theorem widening_selects_signed_or_unsigned(flag: Bool, x: int32, y: uint32) {
    requires x == -1;
    requires y == 4294967295u32;
    ensures flag implies (if flag { x as int64 } else { y as int64 }) == -1i64 by {
        intro();
        rewrite(x, -1);
        solve() using { flag; };
    }
    ensures (not flag) implies (if flag { x as int64 } else { y as int64 }) == 4294967295i64 by {
        intro();
        rewrite(y, 4294967295u32);
        solve() using { not flag; };
    }
}
```

```expect
pass
```
