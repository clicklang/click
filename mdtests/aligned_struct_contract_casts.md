# Struct pointer arithmetic keeps its physical stride inside contract casts

Stepping a struct pointer by a symbolic index displaces it by a multiple of
the struct size. When the alignment divides that size the residue is
unchanged, so `aligned(p, 8)` carries to `p + i`.

```c filename=aligned_symbolic_displacement.c
struct pair {
    int32 a;
    int64 b;
};

int32 element_is_aligned(struct pair *p, int32 i) {
    return ((unsigned long)(p + i) & 7) == 0;
}
```

```click
verifying "aligned_symbolic_displacement.c";

int32 element_is_aligned(struct pair* p, int32 i) {
    requires aligned(p, 8);
    requires 0 <= i and i < 4;
    views p[0..4];
    ensures result == 1;
} by {
    execute();
    have aligned(p + i, 8) by { simp(); }
    have ((uint64)(p + i) & 7) == 0 by { assumption(); }
    simp();
}
```

```expect
pass
```
