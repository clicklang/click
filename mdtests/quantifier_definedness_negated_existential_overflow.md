# Refuting an existential still requires definedness for every candidate

At `INT32_MAX`, `k + 1` is undefined. Its reflexive disequality cannot be
ruled out by treating undefinedness as false.

```click
theorem check_quantifier() {
    ensures not (exists (k: int32) { to_integer(k + 1) != to_integer(k + 1) }) by {
        intro();
        normalize();
    }
}
```

```expect
fail: not established
```
