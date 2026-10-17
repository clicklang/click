# Allocation equality permits access through the explicit void view

The companion original-pointer probe must fail. This C body explicitly widens
its access value; the void-view equality and the sibling permission justify
that access under the approved character/void cast policy.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair, int32* q) {
    return ((int32*)(void*)q)[1];
}
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
pass
```
