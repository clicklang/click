# A pointer integer cannot escape a member of a local aggregate

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe() {
    struct Pair pair = { 11, 22 };
    unsigned long word = (unsigned long)&pair.first;
    return ((int32*)word)[1];
}
```

```click
verifying "probe.c";
int32 probe() {
    ensures result == 22;
} by { execute(); simp(); }
```

```expect
fail: outside
```
