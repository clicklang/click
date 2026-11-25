# Conditional proofs use indexed pointer equality

```c filename=graph_conditions.c
void keep(int32* a, int32* b) { }
```

```click
verifying "graph_conditions.c";

void keep(int32* a, int32* b) {
    requires a == b;
    ensures (if a + 1 == b + 1 { 7 } else { 0 }) == 7;
} by {
    step_until(function.exit);
    close();
}

theorem mixed(a: int32*, b: int32*, x: int32) {
    requires a == b;
    requires x < 0;
    ensures (if x < 0 { if a + 1 == b + 1 { 7 } else { 0 } } else { 0 }) == 7 by {
        close();
    }
}
```

```expect
pass
```
