# An arbitrary type has no known exhaustive constructor list

```click
theorem invalid<T>(x: T) {
    ensures (match x {}) == 0 by close();
}
```

```expect
fail: match
```
