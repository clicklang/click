# A C address comparison cannot transfer a pointer's write designation

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 write_equal(int32* q, int32* p) {
    if (q == p) { *q = 7; return 1; }
    return 0;
}
int32 probe(struct Pair* pair) {
    return write_equal(&pair->first + 1, &pair->second);
}
```

```click
verifying "probe.c";
int32 write_equal(int32* q, int32* p) {
    consumes p[0..1];
} by { execute(); simp(); }
int32 probe(struct Pair* pair) {
    consumes pair->first;
    consumes pair->second;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
