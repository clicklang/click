# A negated float bound admits NaN

```click
theorem nan_can_satisfy_this_premise(x: double) {
    requires not (x <= float64_from_bits(0x3ff0000000000000));
    ensures x > float64_from_bits(0) by {
        normalize() using { not (x <= float64_from_bits(0x3ff0000000000000)); };
    }
}
```

```expect
fail: goal did not normalize to true
```
