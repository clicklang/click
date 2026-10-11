# `simp` closes a 64-bit order chain

`simp()` proves an order goal from a chain of `uint64` or `int64` order
facts, as it does for `int32`: the kernel records the facts its 64-bit order
walk used, and `simp` writes them out as the standard library's
transitivity lemmas (`uint64_lt_le_transitive` and its siblings), each link
stated with `have`. A fact spelled from the other side, `c >= b`, takes part
as `b <= c` does.

`simp_refuses_a_broken_64_bit_order_chain.md` breaks the chain.

```click
theorem two_links(a: uint64, b: uint64, c: uint64) {
    requires a < b;
    requires b <= c;
    ensures a < c by { simp(); }
}
theorem three_links(a: uint64, b: uint64, c: uint64, d: uint64) {
    requires a < b;
    requires b <= c;
    requires c <= d;
    ensures a < d by { simp(); }
}
theorem signed_links(a: int64, b: int64, c: int64, d: int64) {
    requires a < b;
    requires c >= b;
    requires c <= d;
    ensures a < d by { simp(); }
}
theorem written_from_the_other_side(a: uint64, b: uint64, c: uint64) {
    requires a < b;
    requires c >= b;
    ensures a < c by { apply(uint64_lt_le_transitive(a, b, c)) using { a < b; c >= b; } }
}
```

```expect
pass
```
