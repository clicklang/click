# Variable shift counts in machine conditionals

```click
theorem right_int32(flag: Bool, x: int32, z: int32, w: int32) {
    requires 0 <= w;
    requires w < 32;
    requires x == (z >> w);
    ensures flag implies (if flag { x } else { 3 }) == (z >> w) by {
        intro() {
            rewrite(x, z >> w);
            close() using { flag; };
        }
    }
}

theorem right_uint32(flag: Bool, x: uint32, z: uint32, w: uint32) {
    requires w < 32u32;
    requires x == (z >> w);
    ensures flag implies (if flag { x } else { 3u32 }) == (z >> w) by {
        intro() {
            rewrite(x, z >> w);
            close() using { flag; };
        }
    }
}

theorem left_uint32(flag: Bool, x: uint32, z: uint32, w: uint32) {
    requires w < 32u32;
    requires x == (z << w);
    ensures flag implies (if flag { x } else { 3u32 }) == (z << w) by {
        intro() {
            rewrite(x, z << w);
            close() using { flag; };
        }
    }
}

theorem right_int64(flag: Bool, x: int64, z: int64, w: int64) {
    requires 0i64 <= w;
    requires w < 64i64;
    requires x == (z >> w);
    ensures flag implies (if flag { x } else { 3i64 }) == (z >> w) by {
        intro() {
            rewrite(x, z >> w);
            close() using { flag; };
        }
    }
}

theorem right_uint64(flag: Bool, x: uint64, z: uint64, w: uint64) {
    requires w < 64u64;
    requires x == (z >> w);
    ensures flag implies (if flag { x } else { 3u64 }) == (z >> w) by {
        intro() {
            rewrite(x, z >> w);
            close() using { flag; };
        }
    }
}

theorem left_uint64(flag: Bool, x: uint64, z: uint64, w: uint64) {
    requires w < 64u64;
    requires x == (z << w);
    ensures flag implies (if flag { x } else { 3u64 }) == (z << w) by {
        intro() {
            rewrite(x, z << w);
            close() using { flag; };
        }
    }
}
```

```expect
pass
```
