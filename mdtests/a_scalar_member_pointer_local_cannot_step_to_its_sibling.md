# A scalar-member pointer copied to a local cannot step to its sibling

The subobject a pointer designates travels with its value: copying
`&p->first` to a local and adding one still leaves `first`, so the read is
refused as it is for the direct spelling.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) {
    int32* q = &p->first;
    q = q + 1;
    return *q;
}
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
fail: access outside the subobject the pointer designates
```
