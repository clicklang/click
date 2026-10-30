# Quantifier definedness: universal safe

```click
theorem check_quantifier() {
    ensures forall (k: uint8) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) } by { intro(); normalize(); }
}
```

```expect
pass
```
