# A cast contract permits its selected scalar member

```c filename=packed.c
struct pair { int32 first; int32 second; };
int32 read_packed(unsigned long word, struct pair* pair) {
    return ((int32*)(word & ~1))[0];
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long word, struct pair* pair) {
    requires pair != 0;
    requires ((int32*)(word & ~1)) == &pair->first;
    views pair->first;
    ensures result == pair->first;
} by { execute(); simp(); }
```

```expect
pass
```
