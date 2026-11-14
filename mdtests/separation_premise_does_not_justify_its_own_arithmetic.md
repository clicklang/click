# A resource premise cannot justify its own partial endpoint expression

```click
theorem unchecked(p: int32*, q: int32*, n: int32) {
    requires separate(memory(p[n..n + 2]), memory(q[0..1]));
    ensures true;
}
```

```expect
fail: `n + 2` must not overflow
```
