# The uint32 order lemmas state single unsigned steps

An unsigned order is not the signed order of the same operands, so the
`int32` lemmas do not apply to `uint32` values. These are the unsigned
counterparts a proof applies by name: a predecessor, a successor under a
strict bound, a nonzero difference, a chain of two orders, the descent of
a difference from a constant, and one comparison read the other way round.

```click
theorem predecessor(x: uint32) {
    requires x > 0u32;
    ensures x - 1u32 < x by {
        have 0u32 < x by {
            apply(uint32_gt_implies_reversed_lt(x, 0u32)) using { x > 0u32; }
        }
        apply(uint32_positive_predecessor_strictly_decreases(x)) using { 0u32 < x; }
    }
}

theorem successor_within_a_bound(x: uint32) {
    requires x < 4u32;
    ensures x + 1u32 <= 4u32 by {
        apply(uint32_increment_upper_bound(x, 4u32)) using { x < 4u32; }
    }
}

theorem successor_is_larger(x: uint32, n: uint32) {
    requires x < n;
    ensures x < x + 1u32 by {
        apply(uint32_increment_strictly_increases(x, n)) using { x < n; }
    }
}

theorem difference_is_nonzero(x: uint32, n: uint32) {
    requires x < n;
    ensures 0u32 < n - x by {
        apply(uint32_lt_implies_positive_difference(x, n)) using { x < n; }
    }
}

theorem read_the_other_way_round(x: uint32) {
    requires x > 1u32;
    ensures 1u32 < x by {
        apply(uint32_gt_implies_reversed_lt(x, 1u32)) using { x > 1u32; }
    }
}

theorem chained(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by {
        apply(uint32_lt_le_transitive(x, n, 4u32)) using { x < n; n <= 4u32; }
    }
}

theorem difference_from_a_constant_decreases(x: uint32) {
    requires x < 4u32;
    ensures (0u32 - x) + 3u32 < (0u32 - x) + 4u32 by {
        apply(uint32_difference_decreases_after_increment(x, 4u32)) using { x < 4u32; }
    }
}

theorem non_strict_read_the_other_way_round(x: uint32, n: uint32) {
    requires x <= n;
    ensures n >= x by {
        apply(uint32_le_implies_reversed_ge(x, n)) using { x <= n; }
    }
}
```

```expect
pass
```
