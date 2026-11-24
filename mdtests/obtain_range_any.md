# Obtain a witness from a range existential

The witness has the range's index type. Its bounds and predicate body are
available to subsequent checked steps.

```click
theorem signed_range(n: int32, x: int32) {
    requires (0..n).any(|i| { i == x });
    ensures 0 <= x and x < n by {
        let k = obtain((0..n).any(|i| { i == x }));
        have 0 <= k by close();
        have k < n by close();
        have k == x by close();
        rewrite(x, k);
        close();
    }
}

theorem wide_range(n: uint64, x: uint64) {
    requires (4294967296u64..n).any(|k| { k == x });
    ensures 4294967296u64 <= x and x < n by {
        let k = obtain((4294967296u64..n).any(|k| { k == x }));
        have 4294967296u64 <= k by close();
        have k < n by close();
        have k == x by close();
        rewrite(x, k);
        close();
    }
}

theorem nested_range(n: int32, x: int32) {
    requires exists (lo: int32) { (lo..n).any(|lo| { lo == x }) };
    ensures x < n by {
        let (start, k) = obtain(exists (lo: int32) { (lo..n).any(|lo| { lo == x }) });
        have start <= k by close();
        have k == x by close();
        rewrite(x, k);
        close();
    }
}
```

```expect
pass
```
