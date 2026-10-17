# An unchanged pointer integer, including a local copy, retains its member

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair) {
    unsigned long word = (unsigned long)&pair->first;
    unsigned long copy = word;
    return *((int32*)copy);
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair) {
    views pair->first;
    ensures result == pair->first;
} by { execute(); simp(); }
```

```expect
pass
```
