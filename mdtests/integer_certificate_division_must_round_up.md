# Division rounds to the integer bound and no further

`2 * x <= 5` gives `x <= 2` over the integers. Claiming the stronger
`x <= 1` from the same division is refused.

```click
theorem over_rounded(x: Integer) {
    requires 2 * x <= 5;
    ensures x <= 1 by {
        close() using { 2 * x <= 5; };
    }
}
```

```expect
fail: solve
```
