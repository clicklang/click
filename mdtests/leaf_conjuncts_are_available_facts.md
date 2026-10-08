# Leaf conjuncts of a fact are available facts

Recording a conjunction as a fact also records each of its leaf conjuncts,
so every tactic may cite a leaf directly: `assumption()` closes `x <= 5`,
and an arithmetic certificate names `x <= 100` as a premise, with no
`extract`. A conjunct that is itself a conjunction is not a leaf, so it is
not recorded as a fact; `assumption()` still closes it from its leaves, and
`extract` adds it when a `using` list must cite it whole. See
`mdtests/sub_conjunction_closes_by_assumption.md`.

```c filename=leaf_conjuncts_are_available_facts.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "leaf_conjuncts_are_available_facts.c";

theorem leaf(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x <= 5 by assumption();
}

theorem sub_extracted(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x >= 0 and x <= 5 by {
        extract(x >= 0 and x <= 5);
        assumption();
    }
}

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by {
        execute();
        have result >= 1 by {
            arithmetic_certificate signed_int32 {
                premise 0: x <= 100 => x <= 100;
                premise 1: x >= 0 => x >= 0;
                interval_from_affine 1 (x) (0) (2147483647);
                interval_from_affine 0 (x) (-2147483648) (100);
                interval_intersect 2, 3 (0) (100);
                interval_atom (1) (1) (1);
                interval_add_bounded 4, 5 (1) (101);
                affine_conclusion 1 6 => result >= 1;
                conclusion 7;
            }
        }
        assumption();
    }
}
```

```expect
pass
```
