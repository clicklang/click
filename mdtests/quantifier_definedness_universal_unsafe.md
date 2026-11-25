# Quantifier definedness: universal unsafe

```click
theorem check_quantifier() {
    ensures forall (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) } by { intro() { close(); } }
}
```

```expect
fail: not established
```
