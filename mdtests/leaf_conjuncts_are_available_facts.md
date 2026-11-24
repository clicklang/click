# Leaf conjuncts of a fact are available facts

Recording a conjunction as a fact also records each of its leaf conjuncts,
so every tactic may cite a leaf directly: `close()` closes `x <= 5`,
and an explicit arithmetic proof names `x <= 100` as a premise, with no
`have`. A conjunct that is itself a conjunction is not a leaf, so it is
not recorded as a fact; `close()` still closes it from its leaves, and
`have` adds it when a `using` list must cite it whole. See
`mdtests/sub_conjunction_closes_by_known.md`.

```c filename=leaf_conjuncts_are_available_facts.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "leaf_conjuncts_are_available_facts.c";

theorem leaf(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x <= 5 by close();
}

theorem sub_extracted(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x >= 0 and x <= 5 by {
        have x >= 0 and x <= 5;
        close();
    }
}

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by {
        step_until(function.exit);
        have result >= 1 by {
            close() using { x <= 100; x >= 0; };
        }
        close();
    }
}
```

```expect
pass
```
