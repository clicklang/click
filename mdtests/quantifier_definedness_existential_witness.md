# Quantifier definedness: existential witness

```click
theorem check_quantifier() {
    ensures exists (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) } by { witness { k: 0 }; solve(); }
}
```

```expect
pass
```
