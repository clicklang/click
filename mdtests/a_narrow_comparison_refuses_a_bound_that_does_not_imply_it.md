# A narrow comparison refuses a bound that does not imply it

The cited bound `40u8 <= b` allows `b == 45`, so it does not establish
`48u8 <= b`. Deciding a narrow comparison from a cited bound still checks the
bound.

```click
theorem too_weak(b: uint8) {
    requires 40u8 <= b;
    ensures 48u8 <= b by { close() using { 40u8 <= b; }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
