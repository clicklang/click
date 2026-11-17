# A bitwise arm does not justify selecting the wrong branch

```click
theorem wrong_bitwise_arm(flag: Bool, z: uint64) {
    requires not flag;
    ensures (if flag { (z & 7u64) } else { 3u64 }) == 4u64 by {
        normalize() using { not flag; };
    }
}
```

```expect
fail: did not normalize to true
```
