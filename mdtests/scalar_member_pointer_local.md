# Scalar-member pointer domains: local

Copying a scalar-member pointer to a local preserves its domain.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { int32* q = &p->first; q = q + 1; return *q; }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
