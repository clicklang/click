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
    requires ((word & ~1) as (int32 *)) == &pair->first;
    views pair->first;
    views pair->second;
}
```

```expect
fail: outside
```
