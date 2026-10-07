# A narrow cast is not known to be defined without range guards

```click
theorem wrong(x: int32) {
    ensures defined((uint16)x) by { simp(); }
}
```

```expect
fail: could not establish
```
