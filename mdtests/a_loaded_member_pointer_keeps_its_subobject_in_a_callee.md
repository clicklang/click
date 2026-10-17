# A callee retains a loaded pointer’s selected member

```c filename=link.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Holder* h, struct Pair* p) { return *(h->link + 1); }
int32 caller(struct Holder* h, struct Pair* p) {
    h->link = &p->first;
    return probe(h, p);
}
```

```click
verifying "link.c";
int32 probe(struct Holder* h, struct Pair* p) {
    views h->link;
    views p->first;
    views p->second;
    requires h->link == &p->first;
    ensures result == p->second;
} by { execute(); simp(); }
int32 caller(struct Holder* h, struct Pair* p) {
    owns h->link;
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: outside the subobject
```
