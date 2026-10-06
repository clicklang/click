# A sub-conjunction needs `extract`

The negative of `mdtests/leaf_conjuncts_are_available_facts.md`: the leaves
of `(x >= 0 and x <= 5) and y == 1` are available, but the inner
conjunction `x >= 0 and x <= 5` is not a leaf, so `assumption()` cannot
close it until `extract` adds it.

```click
theorem sub(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x >= 0 and x <= 5 by { assumption(); }
}
```

```expect
fail: current goal is a conjunction
```
