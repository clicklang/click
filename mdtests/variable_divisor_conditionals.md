# Variable divisors in machine conditionals

```click
theorem quotient_uint32(flag: Bool, x: uint32, z: uint32, w: uint32) {
    requires x == (z / w);
    ensures flag implies (if flag { x } else { 3u32 }) == (z / w) by {
        intro();
        rewrite(x, z / w);
        solve() using { flag; };
    }
}

theorem remainder_uint32(flag: Bool, x: uint32, z: uint32, w: uint32) {
    requires x == (z % w);
    ensures flag implies (if flag { x } else { 3u32 }) == (z % w) by {
        intro();
        rewrite(x, z % w);
        solve() using { flag; };
    }
}

theorem quotient_uint64(flag: Bool, x: uint64, z: uint64, w: uint64) {
    requires x == (z / w);
    ensures flag implies (if flag { x } else { 3u64 }) == (z / w) by {
        intro();
        rewrite(x, z / w);
        solve() using { flag; };
    }
}

theorem remainder_uint64(flag: Bool, x: uint64, z: uint64, w: uint64) {
    requires x == (z % w);
    ensures flag implies (if flag { x } else { 3u64 }) == (z % w) by {
        intro();
        rewrite(x, z % w);
        solve() using { flag; };
    }
}
```

```expect
pass
```
