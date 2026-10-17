# A C address comparison does not transfer a pointer's designation

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 read_equal(int32* q, int32* p) {
    if (q == p) { return *q; }
    return 0;
}
int32 probe(struct Pair* pair) {
    return read_equal(&pair->first + 1, &pair->second);
}
```

```click
verifying "probe.c";
int32 read_equal(int32* q, int32* p) {
    views p[0..1];
} by { execute(); simp(); }
int32 probe(struct Pair* pair) {
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
