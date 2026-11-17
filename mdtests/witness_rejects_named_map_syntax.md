# The old named witness map is no longer syntax

```click
theorem old_named_witness_map(x: Integer) {
    ensures exists (z: Integer) { z == x } by {
        witness { wrong: x };
    }
}
```

```expect
fail:
```
