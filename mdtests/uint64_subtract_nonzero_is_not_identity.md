# A nonzero unsigned subtraction is not the identity

```click
theorem subtract_one(n: uint64) {
    ensures n - 1u64 == n by close();
}
```

```expect
fail: could not establish `(to_integer(n) - to_integer(1u64)) == to_integer(n)`
```
