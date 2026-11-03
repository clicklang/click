# solve keeps a conjunct antecedent that holds

The antecedent `x != 0 and x <= 200` holds on `pick`'s `x > 100` path when
`x <= 200`, where the result is `2`, so the claim that it is `3` is false
and refused: no conjunct's opposite is a fact there.

```c filename=solve_keeps_a_conjunct_antecedent_that_holds.c
uint32 pick(uint32 x) {
    if (x == 0) {
        return 1;
    } else if (x > 100) {
        return 2;
    } else {
        return 3;
    }
}
```

```click
verifying "solve_keeps_a_conjunct_antecedent_that_holds.c";

uint32 pick(uint32 x) {
    ensures x != 0u32 and x <= 200u32 implies result == 3u32;
}
```

```expect
fail: `ensures x != 0u32 and x <= 200u32 implies result == 3u32` failed
```
