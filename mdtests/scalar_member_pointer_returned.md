# Scalar-member pointer domains: returned

A verified pointer-returning helper retains its selected scalar domain.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32* first(struct Pair* p) { return &p->first; }
int32 probe(struct Pair* p) { return *(first(p) + 1); }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32* first(struct Pair* p) { views p->first; ensures result == &p->first; } by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
