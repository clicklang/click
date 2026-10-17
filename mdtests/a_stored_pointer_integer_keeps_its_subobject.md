# A whole integer store and reload retains the pointer's member bounds

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { unsigned long word; };
int32 probe(struct Pair* pair, struct Holder* h) {
    h->word = (unsigned long)&pair->first;
    unsigned long copy = h->word;
    return ((int32*)copy)[1];
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair, struct Holder* h) {
    views pair->first;
    views pair->second;
    owns h->word;
} by { execute(); simp(); }
```

```expect
fail: outside
```
