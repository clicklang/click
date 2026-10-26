# A one-sided premise still needs the operand bound it is paired with

The negative of
[`arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.md`](arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.md).
Here `n` may be one past the largest four-byte element count, so `i < n`
bounds `i + 1` only by `1073741824`, and for `i == 1073741823` the extent
bound `((i + 1) as uint32) <= 1073741823u32` is false. Intersecting
the direct `0 <= i + 1` with the operands' bound does not reach below the
limit, so the certificate is still refused.

```c filename=arithmetic_one_sided_premise_still_needs_the_operand_bound.c
int32 next_index(int32 i, int32 n) {
    return i + 1;
}
```

```click
verifying "arithmetic_one_sided_premise_still_needs_the_operand_bound.c";

int32 next_index(int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741824;
    ensures to_integer(result) == to_integer(i + 1);
} by {
    have 0 <= to_integer(i + 1) by {
        solve() using { 0 <= i; i < n; n <= 1073741824; };
    }
    have ((i + 1) as uint32) <= 1073741823u32 by {
        solve() using {
            0 <= to_integer(i + 1);
            0 <= i;
            i < n;
            n <= 1073741824;
        };
    }
}
```

```expect
fail: (i + 1) as uint32 <= 1073741823u32
```
