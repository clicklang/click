# Scalar-member pointer domains: stored

A pointer field retains the domain of the complete stored pointer value.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Pair* p, struct Holder* h) { h->link = &p->first; return *(h->link + 1); }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p, struct Holder* h) {
    owns h->link;
    requires separate(memory(h->link), memory(p->first));
    requires separate(memory(h->link), memory(p->second));
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
