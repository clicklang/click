# An int32 range variable is int32 in a call

The variable of `(0..n).all(|k| { ... })` over `int32` bounds is `int32`, so
passing it to a `uint64` parameter is a conversion that must be written.

```click
function g(a: uint64) -> uint64 { a }

theorem narrow(n: int32) {
    requires (0..n).all(|k| { g(k) == g(k) });
    ensures true by { normalize(); }
}
```

```expect
fail: function `g` argument 0 expects uint64, got int32
```
