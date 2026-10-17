# A cast contract retains the pointer's selected member

```c filename=packed.c
struct pair { int32 first; int32 second; };
int32 read_packed(unsigned long word, struct pair* pair) {
    return ((int32*)(word & ~1))[1];
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long word, struct pair* pair) {
    requires pair != 0;
    requires ((int32*)(word & ~1)) == &pair->first;
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: outside
```
