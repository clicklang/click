# A pure nested smart proof uses pointer disequality symmetry

Nested `have` bodies run on `Proof`, including smart tactics. The shared
equality graph recognizes a reversed pointer disequality through the same
condition class. The original C and theorem remain the regression.

```c filename=symmetry.c
int nothing(void) { return 0; }
```

```click
verifying "symmetry.c";

theorem pointer_disequality_symmetry(a: int32*, b: int32*) {
    requires a != b;

    ensures 1 == 1 by {
        have b != a;
        normalize();
    }
}

int nothing() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
