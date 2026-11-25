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
```

```expect
pass
```
