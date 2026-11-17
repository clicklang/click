# The removed extraction tactic is rejected

```click
theorem old_tactic(x: int32) {
    requires x == 0 and x == x;
    ensures x == 0 by { extract(x == 0); }
}
```

```expect
fail: unknown tactic `extract`
```
