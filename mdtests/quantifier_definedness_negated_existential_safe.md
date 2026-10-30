# Quantifier definedness: negated existential safe

```click
theorem check_quantifier() {
    ensures not (exists (k: uint8) { to_uint8(to_integer(k)) != to_uint8(to_integer(k)) }) by { intro(); normalize(); }
}
```

```expect
pass
```
