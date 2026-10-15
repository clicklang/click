# A member pointer stored and reloaded keeps its subobject

Storing `&p->first` in a pointer field and reading it back yields the same
pointer value, including the subobject it designates; one past it is still
not `second`.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Pair* p, struct Holder* h) {
    h->link = &p->first;
    int32* q = h->link;
    return *(q + 1);
}
```

```click
verifying "probe.c";
int32 probe(struct Pair* p, struct Holder* h) {
    views p->first;
    views p->second;
    owns h->link;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
