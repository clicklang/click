# An Integer callback fold uses its selected predecessor guard

```click
function total(step: fn(Integer, Integer) -> Integer, lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, step)
}
theorem append(lo: Integer, hi: Integer) {
    requires lo <= hi;
    ensures total(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi + 1)
        == total(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi) + hi by {
        have hi + 1 - 1 == hi by close();
        have lo <= hi + 1 - 1 by close();
        unfold(total(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi + 1));
        close();
    }
}
```

```expect
pass
```
