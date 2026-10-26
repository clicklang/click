# A literal true disjunction does not require the unused native division

A literally true left side leaves no case for the right side, so
`0u32 == 0u32 or 5u32 / 0u32 == 1u32` lowers to its left side. A left side
that only the facts make true keeps the written disjunction: the proof
states it, and the right side's division is owed only where the left fails.

```click
theorem guarded(x: uint32) {
    requires x == 0u32 or 5u32 / x == 1u32;
    ensures 1 == 1 by solve();
}

theorem zero_instance() {
    ensures 1 == 1 by apply(guarded(0u32));
}

theorem known_zero_instance(x: uint32) {
    requires x == 0u32;
    ensures 1 == 1 by {
        have x == 0u32 or 5u32 / x == 1u32 by {
            have x == 0u32;
            assumption();
        }
        apply(guarded(x));
    }
}
```

```expect
pass
```
