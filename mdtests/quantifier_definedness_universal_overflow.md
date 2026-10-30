# A universal requires a defined body for every candidate

Reflexivity does not make signed overflow defined at `INT32_MAX`.

```click
theorem check_quantifier() {
    ensures forall (k: int32) { to_integer(k + 1) == to_integer(k + 1) } by {
        intro();
        normalize();
    }
}
```

```expect
fail: not established
```
