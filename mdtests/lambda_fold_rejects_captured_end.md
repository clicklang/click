# A lambda fold step that captures the end has no predecessor-call law

An alias must not hide a capture from `peel`'s append-law side condition.
Changing the end argument would change every cell's body, so the shorter
fold cannot be restated as a call at the predecessor endpoint.

```click
function captured_end(lo: uint64, hi: uint64) -> Integer {
    let step = |acc: Integer, k: uint64| -> Integer { acc + to_integer(hi) };
    (lo..hi).fold(0, step)
}

theorem not_a_predecessor_call(lo: uint64, hi: uint64) {
    requires lo <= hi;
    requires hi < 18446744073709551615u64;
    ensures captured_end(lo, hi + 1u64) == captured_end(lo, hi) + to_integer(hi) by {
        peel(captured_end(lo, hi + 1u64)) using { lo <= hi; hi < 18446744073709551615u64; };
        solve();
    }
}
```

```expect
fail: the fold's body also reads `hi`
```
