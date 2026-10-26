# A signed certificate concludes a `uint32` order from intervals of known sign

`interval_compare L, R ule` (and `ult`) concludes the `uint32` order of two
words from their checked signed intervals: a non-negative interval reads the
same as unsigned, and a negative one `2^32` higher. Here `length` is in
`[0, 536870911]`, so `length as uint32` is at most `1073741823u32`. This is
the certificate `solve() using` writes for
[`arithmetic_unsigned_range_bound.md`](arithmetic_unsigned_range_bound.md);
an interval of both signs has no unsigned reading, and the step refuses it.

```click
theorem allocation_range_fits(length: int32) {
    requires 0 <= length;
    requires length <= 536870911;
    ensures (length as uint32) <= 1073741823u32 by {
        arithmetic_certificate signed_int32 {
            premise 0: 0 <= length => 0 <= length;
            premise 1: length <= 536870911 => length <= 536870911;
            interval_from_affine 0 (length) (0) (2147483647);
            interval_from_affine 1 (length) (-2147483648) (536870911);
            interval_intersect 2, 3 (0) (536870911);
            interval_atom (1073741823) (1073741823) (1073741823);
            interval_compare 4, 5 ule => (length as uint32) <= 1073741823u32;
            conclusion 6;
        }
    }
}
```

```expect
pass
```
