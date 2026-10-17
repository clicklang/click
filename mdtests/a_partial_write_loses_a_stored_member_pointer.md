# A byte overwrite invalidates a complete stored pointer

```c filename=partial.c
struct pair { int32 first; int32 second; };
struct holder { int32 *p; };
int32 read_member(struct holder *h, struct pair *pair) {
    unsigned char* bytes;
    h->p = &pair->first;
    bytes = (unsigned char*)(void*)&h->p;
    bytes[4] = 7;
    return h->p[0];
}
```

```click
verifying "partial.c";
int32 read_member(struct holder* h, struct pair* pair) {
    owns h->p;
    views pair->first;
    views pair->second;
    ensures result == pair->first;
} by { execute(); simp(); }
```

```expect
fail: missing resource
```
