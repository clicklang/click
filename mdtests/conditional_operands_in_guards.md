# Machine conditionals as guard comparison operands

```click
theorem compare_conditional_uint32(inner: Bool, y: uint32, z: uint32, w: uint32) {
    requires (if inner { y } else { z }) < w;
    ensures (if (if inner { y } else { z }) < w { y } else { 3u32 }) == y by {
        close() using { (if inner { y } else { z }) < w; };
    }
}

theorem compare_conditional_int64(y: int64, z: int64, w: int64) {
    requires w != (if y < z { y } else { z });
    ensures (if w != (if y < z { y } else { z }) { y } else { 3i64 }) == y by {
        close() using { w != (if y < z { y } else { z }); };
    }
}
```

```expect
pass
```
