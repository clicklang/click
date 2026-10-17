# A whole stored pointer integer can still read its original member

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { unsigned long word; };
int32 probe(struct Pair* pair, struct Holder* h) {
    h->word = (unsigned long)&pair->first;
    unsigned long copy = h->word;
    return *((int32*)copy);
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair, struct Holder* h) {
    views pair->first;
    owns h->word;
    ensures result == pair->first;
} by { execute(); simp(); }
```

```expect
pass
```
