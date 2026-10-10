# A nonzero unsigned subtraction is not the identity

```click
theorem subtract_one(n: uint64) {
    ensures n - 1u64 == n by normalize();
}
```

```expect
fail: goal did not normalize to true
```
