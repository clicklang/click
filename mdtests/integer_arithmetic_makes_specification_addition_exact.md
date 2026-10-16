# integer arithmetic makes specification addition exact

Under `arithmetic "integer";` a specification comparison that does
arithmetic on machine integers is an Integer comparison: `x + 1` is the
mathematical successor of `x`, with no overflow obligation, so `x + 1 > x`
holds for every `int32`, and for every `uint32` too, where C arithmetic
would wrap. Without the directive the same claim is C arithmetic
(`mdtests/machine_specification_addition_needs_its_overflow_bound.md`).

```click
arithmetic "integer";

theorem signed_successor_is_greater(x: int32) {
    ensures x + 1 > x by auto;
}

theorem unsigned_successor_is_greater(x: uint32) {
    ensures x + 1 > x by auto;
}

theorem sums_of_bounded_values_are_exact(a: int32, b: int32) {
    requires 0 <= a;
    requires 0 <= b;
    ensures a + b >= a by auto;
}
```

```expect
pass
```
