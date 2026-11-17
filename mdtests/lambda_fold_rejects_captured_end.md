# A lambda fold that captures its end has no predecessor-call law

Changing the end argument changes every cell's body. Ordinary `unfold` retains
the defining equation because the shorter fold cannot be restated as a call
at the predecessor endpoint. It must not justify the false append claim.

```click
function captured_end(lo: uint64, hi: uint64) -> Integer {
    let step = |acc: Integer, k: uint64| -> Integer { acc + to_integer(hi) };
    (lo..hi).fold(0, step)
}

theorem not_a_predecessor_call(lo: uint64, hi: uint64) {
    requires lo <= hi;
    requires hi < 18446744073709551615u64;
    ensures captured_end(lo, hi + 1u64) == captured_end(lo, hi) + to_integer(hi) by {
        unfold(captured_end(lo, hi + 1u64));
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
