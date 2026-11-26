# An unused generic theorem cannot hide an invalid proof

```click
theorem invalid<T>(x: T, y: T) {
    ensures x == y by close();
}
```

```expect
fail: invalid.ensures_0
```
