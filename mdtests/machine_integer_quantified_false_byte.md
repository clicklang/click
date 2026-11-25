# machine integer quantified false byte

```click
theorem bad(n: uint8) {
    ensures exists (x: uint8) { x + 1 == n } by {
        witness(n);
        close();
    }
}
```

```expect
fail: could not establish `(to_integer(n) + 1) == to_integer(n)`
```
