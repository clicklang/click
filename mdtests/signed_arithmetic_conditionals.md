# Signed arithmetic in machine conditionals

```click
theorem add_int32(flag: Bool, x: int32, z: int32, w: int32) {
    requires defined(z + w);
    requires x == ((z + w) as int32);
    ensures flag implies (if flag { x } else { 3 }) == ((z + w) as int32) by {
        intro();
        rewrite(x, ((z + w) as int32));
        normalize() using { flag; };
    }
}

theorem sub_int32(flag: Bool, x: int32, z: int32, w: int32) {
    requires defined(z - w);
    requires x == ((z - w) as int32);
    ensures flag implies (if flag { x } else { 3 }) == ((z - w) as int32) by {
        intro();
        rewrite(x, ((z - w) as int32));
        normalize() using { flag; };
    }
}

theorem mul_int32(flag: Bool, x: int32, z: int32, w: int32) {
    requires defined(z * w);
    requires x == ((z * w) as int32);
    ensures flag implies (if flag { x } else { 3 }) == ((z * w) as int32) by {
        intro();
        rewrite(x, ((z * w) as int32));
        normalize() using { flag; };
    }
}

theorem add_int64(flag: Bool, x: int64, z: int64, w: int64) {
    requires defined(z + w);
    requires x == ((z + w) as int64);
    ensures flag implies (if flag { x } else { 3i64 }) == ((z + w) as int64) by {
        intro();
        rewrite(x, ((z + w) as int64));
        normalize() using { flag; };
    }
}

theorem sub_int64(flag: Bool, x: int64, z: int64, w: int64) {
    requires defined(z - w);
    requires x == ((z - w) as int64);
    ensures flag implies (if flag { x } else { 3i64 }) == ((z - w) as int64) by {
        intro();
        rewrite(x, ((z - w) as int64));
        normalize() using { flag; };
    }
}

theorem mul_int64(flag: Bool, x: int64, z: int64, w: int64) {
    requires defined(z * w);
    requires x == ((z * w) as int64);
    ensures flag implies (if flag { x } else { 3i64 }) == ((z * w) as int64) by {
        intro();
        rewrite(x, ((z * w) as int64));
        normalize() using { flag; };
    }
}
```

```expect
pass
```
