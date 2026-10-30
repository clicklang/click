# Quantifier definedness: nested counterexample

```click
theorem check_quantifier() {
    ensures forall (a: uint8) { not (forall (k: int32) { to_uint8(to_integer(k)) != to_uint8(to_integer(k)) }) } by { intro(); witness { k: 0 }; solve(); }
}
```

```expect
pass
```
