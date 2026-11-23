# A negated comparison admits NaN and supplies no ordered bound

```click
theorem negated_comparison(x: double) {
    requires not (x > float64_from_bits(0x3ff0000000000000));
    ensures -x >= float64_from_bits(0xbff0000000000000) by {
        normalize() using { not (x > float64_from_bits(0x3ff0000000000000)); };
    }
}
```

```expect
fail: goal did not normalize to true
```
