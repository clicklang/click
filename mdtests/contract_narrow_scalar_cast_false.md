# A narrow cast does not establish a false value

```click
theorem wrong() {
    ensures (uint16)65521 == (uint16)0 by { simp(); }
}
```

```expect
fail: it is false at this point
```
