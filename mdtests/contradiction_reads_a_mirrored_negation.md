# Mirrored comparisons establish false

Opposite equality facts establish `false` even when one comparison writes
the operands in the other order.

```c filename=contradiction_reads_a_mirrored_negation.c
void unused(void) {}
```

```click
verifying "contradiction_reads_a_mirrored_negation.c";

theorem mirrored_negation(x: int32) {
    requires x == 3;
    requires 3 != x;
    ensures false by { close(); }
}

theorem mirrored_positive(x: int32) {
    requires 3 == x;
    requires x != 3;
    ensures false by { close(); }
}
```

```expect
pass
```
