# A contract exit cannot return a composite and each of its two body children

`wrap2(p)` owns two cells. Returning the composite and both cells counts
each cell twice.

```c filename=composite_two_children.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap2(p: int32*) {
    owns p[0..1];
    owns p[1..2];
}
verifying "composite_two_children.c";
int32 f(int32* p) {
    owns wrap2(p);
    produces p[0..1];
    produces p[1..2];
} by auto;
```

```expect
fail: missing resource fact
```
