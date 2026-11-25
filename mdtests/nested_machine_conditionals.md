# Nested machine conditionals

```click
theorem select_inner(flag: Bool, inner: Bool, x: int32, y: int32) {
    requires flag;
    requires inner;
    ensures (if flag { if inner { x } else { y } } else { 3 }) == x by {
        close();
    }
}

theorem select_inner_comparison(flag: Bool, x: uint64, y: uint64) {
    requires flag;
    requires x < y;
    ensures (if flag { if x < y { x } else { y } } else { 3u64 }) == x by {
        close();
    }
}

theorem nested_true(x: int32, y: int32) {
    requires x < y;
    requires y == 5;
    ensures (if x < y { if y == 5 { 8 } else { 3 } } else { 0 }) == 8 by {
        close() using { x < y; y == 5; };
    }
}
theorem nested_false(flag: Bool, x: int32, y: int32) {
    requires not(flag);
    requires x < y;
    ensures (if flag { 2 } else { if x < y { 3 } else { 4 } }) == 3 by {
        close() using { not(flag); x < y; };
    }
}
theorem nested_wide(flag: Bool, x: uint64, y: uint64) {
    requires flag;
    requires x < y;
    ensures (if flag { if x < y { x } else { y } } else { 3u64 }) == x by {
        close() using { flag; x < y; };
    }
}
```

```expect
pass
```
