# Equal byte views do not widen the original opaque pointer

Converting to a byte pointer forms the byte view of the allocation (C11
6.3.2.3p7), so the two views have the allocation's bounds. Equating them can
establish allocation origin, but says nothing about the original `q`'s
selected bounds. Its own scalar permission and the sibling permission must not
merge into a longer permission carrying q's opaque bounds.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair, int32* q) { return q[1]; }
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair, int32* q) {
    requires q as (uint8 *) == pair as (uint8 *);
    views q[0];
    views pair->second;
}
```

```expect
fail: missing resource
```
