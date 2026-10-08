# Order chains of three facts close

A chain of order facts composes the same way however long it is, and an
unsigned chain the same way as a signed one. `simp` finds the chain and
names a transitivity lemma per edge, `int32_*` or `uint32_*` by the
operands' type; `arithmetic() using` adds the premises it lists.

```click
theorem signed_by_simp(x: int32, a: int32, b: int32) {
    requires x < a;
    requires a <= b;
    requires b <= 4;
    ensures x < 4 by simp;
}

theorem unsigned_by_simp(x: uint32, a: uint32, b: uint32) {
    requires x < a;
    requires a <= b;
    requires b <= 4u32;
    ensures x < 4u32 by simp;
}

theorem signed_by_arithmetic(x: int32, a: int32, b: int32) {
    requires x < a;
    requires a <= b;
    requires b <= 4;
    ensures x < 4 by { arithmetic() using { x < a; a <= b; b <= 4; } }
}

theorem unsigned_by_arithmetic(x: uint32, a: uint32, b: uint32) {
    requires x < a;
    requires a <= b;
    requires b <= 4u32;
    ensures x < 4u32 by { arithmetic() using { x < a; a <= b; b <= 4u32; } }
}

theorem four_edges_by_arithmetic(x: int32, a: int32, b: int32, c: int32) {
    requires x < a;
    requires a <= b;
    requires b <= c;
    requires c <= 4;
    ensures x < 4 by { arithmetic() using { x < a; a <= b; b <= c; c <= 4; } }
}
```

```expect
pass
```
