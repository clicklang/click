# Copying an aggregate retains a complete pointer integer

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { unsigned long word; };
int32 probe(struct Pair* pair, struct Holder* a, struct Holder* b) {
    a->word = (unsigned long)&pair->first;
    *b = *a;
    return *((int32*)b->word);
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair, struct Holder* a, struct Holder* b) {
    views pair->first;
    owns a->word;
    owns b->word;
    ensures result == pair->first;
} by { execute(); simp(); }
```

```expect
pass
```
