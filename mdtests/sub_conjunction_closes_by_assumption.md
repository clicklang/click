# A sub-conjunction closes by `assumption`

The companion of `mdtests/leaf_conjuncts_are_available_facts.md`: the leaves
of `(x >= 0 and x <= 5) and y == 1` are available facts. The inner
conjunction `x >= 0 and x <= 5` is not itself recorded, but `assumption()`
closes a conjunction whose every side is a fact, so it needs no `extract`.

```click
theorem sub(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x >= 0 and x <= 5 by assumption();
}
```

```expect
pass
```
