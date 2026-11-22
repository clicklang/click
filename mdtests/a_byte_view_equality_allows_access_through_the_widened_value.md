# Byte-view equality permits access through the C byte view

The companion original-pointer probe
(`an_equality_of_byte_views_does_not_extend_the_original_pointer.md`) must
fail. This C body forms the byte view itself, `(char*)(void*)q`, which has the
allocation's bounds (C11 6.3.2.3p7); the byte-view equality and the sibling
permission justify the access through it.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair, int32* q) {
    return ((int32*)(void*)(char*)(void*)q)[1];
}
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
pass
```
