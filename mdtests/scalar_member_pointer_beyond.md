# Scalar-member pointer domains: beyond

A scalar-member pointer cannot be formed beyond its one-past endpoint.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32* probe(struct Pair* p) { return &p->first + 2; }
```

```click
verifying "probe.c";
int32* probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
