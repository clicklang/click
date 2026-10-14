# Cached reads preserve return completion

Unfolding the returned resource names its range's existing reads. Refolding
and proving the return claims must certify against the same program state,
even though its memory now holds those read caches.

```c filename=cached-return.c
int32 wrapper(int32* p) { return idle(p); }
```

```click
verifying "cached-return.c";
resource segment(p: int32*) {
    field value: int32;
    owns p[0..2];
    fact value == 0;
}
extern int32 idle(int32* p) {
    owns data: segment(p);
    ensures result == 0;
}
int32 wrapper(int32* p) {
    owns data: segment(p);
    ensures data.value == 0;
    ensures result == 0;
} by {
    step(idle(p), { data: data });
    step();
    unfold(data);
    let data = fold(segment(p), { value: 0 });
    simp();
}
```

```expect
pass
```
