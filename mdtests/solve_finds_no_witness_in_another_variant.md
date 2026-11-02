# solve finds no witness in another variant

A fact that fixes `r` to `Err(5)` gives no payload for
`exists (v: int32) { r == Result<int32, uint8>::Ok(v) }`, which is false: the
witness is read only off a constructor of the variant the goal names.

```click
theorem no_witness(r: Result<int32, uint8>) {
    requires r == Result<int32, uint8>::Err(5u8);
    ensures exists (v: int32) { r == Result<int32, uint8>::Ok(v) } by { solve(); }
}
```

```expect
fail: could not establish `exists (v: int32) { r == Result<int32, uint8>::Ok(v) }`
```
