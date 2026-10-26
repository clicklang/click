# An unsigned interval comparison of unknown sign is refused

The negative beside
[`a_signed_certificate_concludes_a_uint32_order_from_intervals_of_known_sign.md`](a_signed_certificate_concludes_a_uint32_order_from_intervals_of_known_sign.md).
Without `0 <= length` the interval of `length` holds negative words, which
are above `1073741823u32` as unsigned, so `interval_compare ... ule` refuses
the step.

```click
theorem allocation_range_fits(length: int32) {
    requires length <= 536870911;
    ensures (length as uint32) <= 1073741823u32 by {
        arithmetic_certificate signed_int32 {
            premise 0: length <= 536870911 => length <= 536870911;
            interval_from_affine 0 (length) (-2147483648) (536870911);
            interval_atom (1073741823) (1073741823) (1073741823);
            interval_compare 1, 2 ule => (length as uint32) <= 1073741823u32;
            conclusion 3;
        }
    }
}
```

```expect
fail: node 3 does not state what its rule derives from its inputs
```
