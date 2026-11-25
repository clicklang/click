# Arithmetic-free Integer witness goals outside the current pure fragment are rejected

```click
theorem integer_exists_witness_false(x: Integer) {
    ensures exists (z: Integer) { z == 0 } by {
        witness(x);
        close();
    }
}
```

```expect
fail: could not establish `x == 0`
```
