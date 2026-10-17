# Numeric equality with a pointer address does not supply its bounds

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(unsigned long word, struct Pair* pair) {
    return *((int32*)word);
}
```

```click
verifying "probe.c";
int32 probe(uint64 word, struct Pair* pair) {
    requires word == address(pair);
    views pair->first;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
