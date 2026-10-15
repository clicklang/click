# Scalar-member pointer domains: direct

A pointer one past a scalar member cannot read its sibling.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { return *(&p->first + 1); }
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
