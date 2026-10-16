# Numeric arithmetic does not recreate a pointer's bounds

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair) {
    unsigned long word = (unsigned long)&pair->first;
    return *((int32*)(word + 0));
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair) {
    views pair->first;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
