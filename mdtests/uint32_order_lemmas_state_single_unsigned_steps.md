# Single unsigned uint32 steps close by auto

An unsigned order is not the signed order of the same operands. Each single
unsigned step closes by `auto` through the Integer readings of its
operands: a predecessor, a successor under a strict bound, a nonzero
difference, a chain of two orders, the descent of a difference from a
constant, and one comparison read the other way round.

```click
theorem predecessor(x: uint32) {
    requires x > 0u32;
    ensures to_integer(x - 1u32) < to_integer(x) by auto();
}

theorem successor_within_a_bound(x: uint32) {
    requires x < 4u32;
    ensures to_integer(x + 1u32) <= to_integer(4u32) by auto();
}

theorem successor_is_larger(x: uint32, n: uint32) {
    requires x < n;
    ensures to_integer(x) < to_integer(x + 1u32) by auto();
}

theorem difference_is_nonzero(x: uint32, n: uint32) {
    requires x < n;
    ensures to_integer(0u32) < to_integer(n - x) by auto();
}

theorem read_the_other_way_round(x: uint32) {
    requires x > 1u32;
    ensures 1u32 < x by auto();
}

theorem chained(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by auto();
}

theorem difference_from_a_constant_decreases(x: uint32) {
    requires x < 4u32;
    ensures to_integer((0u32 - x) + 3u32) < to_integer((0u32 - x) + 4u32) by auto();
}

theorem non_strict_read_the_other_way_round(x: uint32, n: uint32) {
    requires x <= n;
    ensures n >= x by auto();
}
```

```expect
pass
```
