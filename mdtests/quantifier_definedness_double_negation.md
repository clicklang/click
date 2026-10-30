# Quantifier definedness: double negation

```click
theorem check_quantifier() {
    ensures not (not (exists (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) })) by { witness { k: 0 }; solve(); }
}
```

```expect
pass
```
