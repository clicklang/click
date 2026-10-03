# simp closes single unsigned steps

An unsigned order is the signed order of sign-flipped operands, which
`simp`'s arithmetic treats as opaque atoms. A goal that is one step of
`uint32` arithmetic from an exact fact is closed with the lemma that states
that step, so `simp` does not need the lemma named.

```click
theorem predecessor(x: uint32) {
    requires x > 0u32;
    ensures x - 1u32 < x by { simp(); }
}

theorem successor_within_a_bound(x: uint32) {
    requires x < 4u32;
    ensures x + 1u32 <= 4u32 by { simp(); }
}

theorem read_the_other_way_round(x: uint32) {
    requires x > 1u32;
    ensures 1u32 < x by { simp(); }
}

theorem difference_decreases(x: uint32, n: uint32) {
    requires x < n;
    ensures (n - x) - 1u32 < n - x by { simp(); }
}

theorem difference_from_a_constant_decreases(x: uint32) {
    requires x < 4u32;
    ensures (0u32 - x) + 3u32 < (0u32 - x) + 4u32 by { simp(); }
}
```

```expect
pass
```
