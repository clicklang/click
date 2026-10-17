# An incoming pointer's value equality retains its scalar subobject

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(int32* q, struct Pair* pair) { return q[1]; }
```

```click
verifying "probe.c";
int32 probe(int32* q, struct Pair* pair) {
    requires q == &pair->first;
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: outside
```
