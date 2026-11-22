# A cast through `void *` keeps a member pointer's bounds

C gives a conversion to `void *` no meaning beyond its round trip (C11
6.3.2.3p1), so `(int32*)(void*)&p->first` is the same pointer as `&p->first`.
Reading it past `first` is outside the subobject it designates, though
`p->second` is at that address and the function holds it. Only a conversion to a character
pointer forms a byte view of the allocation
(`a_byte_view_equality_allows_access_through_the_widened_value.md`).

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) {
    return ((int32*)(void*)&p->first)[1];
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
}
```

```expect
fail: access outside the subobject the pointer designates
```
