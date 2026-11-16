# Legacy peel syntax compatibility

Ordinary proofs use `unfold`. This fixture supplies the checked positive
example for the legacy public syntax until that syntax is removed.

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem legacy_empty(lo: int32, hi: int32) {
    requires hi <= lo;
    ensures tally(lo, hi) == 0 by {
        peel(tally(lo, hi)) using { hi <= lo; };
        normalize();
    }
}
```

```expect
pass
```
