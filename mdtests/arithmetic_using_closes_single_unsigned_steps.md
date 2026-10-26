# `solve() using` closes single unsigned steps

An unsigned order is a `uint32` order, whose wrapping steps the arithmetic
certificates do not relate. A goal that is one step of
`uint32` arithmetic from a listed premise is closed with the lemma that
states that step, as a bare `solve()` closes it from an available fact. The premise
must be listed: `solve() using` uses exactly what it is given.

```click
theorem predecessor(x: uint32) {
    requires x > 0u32;
    ensures x - 1u32 < x by { solve() using { x > 0u32; }; }
}

theorem successor_within_a_bound(x: uint32) {
    requires x < 4u32;
    ensures x + 1u32 <= 4u32 by { solve() using { x < 4u32; }; }
}

theorem read_the_other_way_round(x: uint32) {
    requires x > 1u32;
    ensures 1u32 < x by { solve() using { x > 1u32; }; }
}

theorem difference_decreases(x: uint32, n: uint32) {
    requires x < n;
    ensures (n - x) - 1u32 < n - x by { solve() using { x < n; }; }
}

theorem difference_from_a_constant_decreases(x: uint32) {
    requires x < 4u32;
    ensures (0u32 - x) + 3u32 < (0u32 - x) + 4u32 by { solve() using { x < 4u32; }; }
}
```

```expect
pass
```
