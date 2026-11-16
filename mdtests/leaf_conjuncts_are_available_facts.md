# Leaf conjuncts of a fact are available facts

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=leaf_conjuncts_are_available_facts.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "leaf_conjuncts_are_available_facts.c";

theorem leaf(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x <= 5 by known();
}

theorem sub_extracted(x: int32, y: int32) {
    requires (x >= 0 and x <= 5) and y == 1;
    ensures x >= 0 and x <= 5 by {
        extract(x >= 0 and x <= 5);
        known();
    }
}

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by {
        step_until(function.exit);
        have result >= 1 by {
            solve() using { x <= 100; x >= 0; };
        }
        known();
    }
}
```

```expect
pass
```
