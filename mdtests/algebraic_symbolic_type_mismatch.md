# symbolic algebraic values reject mismatched types

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

theorem mismatched(m: Maybe<int32>) {
    ensures m == Maybe<uint32>::None by simp();
}
```

```expect
fail: `Maybe<int32>` and `Maybe<uint32>`
```
