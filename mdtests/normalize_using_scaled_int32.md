# Equal int32 indices give equal pointer offsets

```c filename=scaled_int32.c
void keep(int32* p, int32 i, int32 j, int32 k) { }
```

```click
verifying "scaled_int32.c";

void keep(int32* p, int32 i, int32 j, int32 k) {
    requires i == j;
    requires j == k;
    ensures p + i == p + k;
} by {
    execute();
    normalize() using { }
}

theorem choose(p: int32*, i: int32, j: int32) {
    requires i == j;
    ensures (if p + i == p + j { 7 } else { 0 }) == 7 by {
        normalize() using { }
    }
}

theorem literal(p: int32*, i: int32) {
    requires i == 1;
    ensures p + i == p + 1 by {
        normalize() using { }
    }
}
```

```expect
pass
```
