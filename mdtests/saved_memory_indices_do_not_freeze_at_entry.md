# Saved memory indices do not freeze at entry

After incrementing the index, both descriptors name cell one. Saving the base
must not save the index too and thereby make these cells appear disjoint.

```c filename=saved_overlap.c
void advance(int *p, int i) { i++; }
```

```click
verifying "saved_overlap.c";
void advance(int32 *p, int32 i) { ensures true; requires i == 0; } by {
    step();
    have i == 1;
    have separate(memory(old(p)[i]), memory(old(p)[1])) by { normalize(); }
}
```

```expect
fail: goal did not normalize to true
```
