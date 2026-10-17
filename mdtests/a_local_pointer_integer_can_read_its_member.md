# A pointer integer can still read its original local member

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe() {
    struct Pair pair = { 11, 22 };
    unsigned long word = (unsigned long)&pair.first;
    return *((int32*)word);
}
```

```click
verifying "probe.c";
int32 probe() {
    ensures result == 11;
} by { execute(); simp(); }
```

```expect
pass
```
