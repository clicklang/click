# A numeric pointer address remains usable for C comparison

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair) {
    int32* q = &pair->first;
    unsigned long word = (unsigned long)q;
    return (int32*)(word + 0) == q;
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair) {
    views pair->first;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
