# Signed arithmetic preserves the checked sum after bounded subtraction

The generated addition certificate must retain its normalized affine claim,
including when the final goal spells partially evaluated signed operations.

```c filename=child-sum.c
int32 f(int32 x) { return 0; }
```

```click
verifying "child-sum.c";
int32 f(int32 x) { requires 4 <= x; requires x <= 8; ensures result == 0; } by {
 have (8 - x) <= (8 - x) + 4 by { arithmetic() using { 4 <= x; x <= 8; } }
 execute(); simp();
}
```

```expect
pass
```
