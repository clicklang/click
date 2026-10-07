# Both obtained witnesses resolve in a contradiction

```click
theorem obtained_pair() {
    requires exists (a: int32, b: int32) { a == b and a != b };
    ensures 0 == 1 by {
        obtain (k: int32, m: int32) { k == m and k != m }
        have k == m by { assumption(); }
        have k != m by { assumption(); }
        contradiction(k == m);
    }
}
```

```expect
pass
```
