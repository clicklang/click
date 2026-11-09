# A 128-bit order closes through its Integer reading

A 128-bit comparison is held in its Integer reading, `to_integer(a) <
to_integer(b)`, since the kernel's order reasoning has no 128-bit nodes
(`representation::spells_comparison_natively`). `solve` refutes such a goal
with the Integer certificate, and spells the native premises and goal it
cites, written `a < b`, as those observations, as it does at 64 bits: an
`add` of `a < b` and a constant bound is the sum of `to_integer(a)` and the
constant, since `a + -1` has no 128-bit operation to lower to.

`a_128_bit_order_does_not_give_a_strict_order.md` is the refused
counterpart.

```click
theorem less_than_gives_less_equal(a: int128, b: int128) {
    requires a < b;
    ensures a <= b;
}

theorem less_equal_transitive(a: uint128, b: uint128, c: uint128) {
    requires a <= b;
    requires b <= c;
    ensures a <= c;
}

theorem mixed_transitive(a: int128, b: int128, c: int128) {
    requires a < b;
    requires b <= c;
    ensures a < c;
    ensures c >= a;
}
```

```expect
pass
```
