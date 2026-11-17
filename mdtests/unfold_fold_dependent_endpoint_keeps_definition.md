# A fold whose body reads its endpoint still exposes its definition

```click
function weighted(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(hi) })
}
theorem weighted_definition(lo: int32, hi: int32) {
    requires lo < hi;
    ensures weighted(lo, hi) == (lo..hi).fold(0, |acc, k| { acc + to_integer(hi) }) by {
        unfold(weighted(lo, hi));
        normalize();
    }
}
```

```expect
pass
```
