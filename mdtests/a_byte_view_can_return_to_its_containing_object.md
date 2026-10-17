# An explicit byte view retains the complete object's extent

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* pair) {
    unsigned char* bytes = (unsigned char*)(void*)&pair->first;
    return *(int32*)(void*)(bytes + sizeof(int32));
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* pair) {
    views pair->first;
    views pair->second;
    ensures result == pair->second;
} by { execute(); simp(); }
```

```expect
pass
```
