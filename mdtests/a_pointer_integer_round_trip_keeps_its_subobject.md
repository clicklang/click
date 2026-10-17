# A pointer's integer round trip retains its scalar subobject

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair) {
    int32* q = &pair->first;
    unsigned long word = (unsigned long)q;
    return ((int32*)word)[1];
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair) {
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: outside
```
