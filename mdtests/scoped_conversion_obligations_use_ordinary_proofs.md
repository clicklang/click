# A quantified conversion requirement uses ordinary proof checking

```click
theorem scoped_conversion(j: int32) {
    requires 0 <= j and j <= 255;
    ensures 0 == 0 by {
        have forall (k: int32) {
            k < j implies to_uint8(to_integer(j)) == to_uint8(to_integer(j))
        } by { intro(); intro(); normalize(); }
        normalize();
    }
}
```

```expect
pass
```
