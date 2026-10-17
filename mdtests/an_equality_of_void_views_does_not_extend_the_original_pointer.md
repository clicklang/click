# Equal void views do not widen the original opaque pointer

The void casts explicitly select the enclosing allocation. Equating those
views can establish allocation origin, but says nothing about the original
`q`'s selected extent. Its own scalar permission and the sibling permission
must not merge into a longer permission carrying q's opaque extent.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair, int32* q) { return q[1]; }
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair, int32* q) {
    requires (void*)q == (void*)pair;
    views q[0];
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
