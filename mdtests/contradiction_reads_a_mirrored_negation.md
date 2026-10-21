# contradiction reads a mirrored negation

`contradiction(P)` finds `P` and its negation in any of their spellings,
including an equality's or disequality's mirrored orientation.

```c filename=contradiction_reads_a_mirrored_negation.c
void unused(void) {}
```

```click
verifying "contradiction_reads_a_mirrored_negation.c";

theorem mirrored_negation(x: int32) {
    requires x == 3;
    requires 3 != x;
    ensures false by { contradiction(x == 3); }
}

theorem mirrored_positive(x: int32) {
    requires 3 == x;
    requires x != 3;
    ensures false by { contradiction(x == 3); }
}
```

```expect
pass
```
