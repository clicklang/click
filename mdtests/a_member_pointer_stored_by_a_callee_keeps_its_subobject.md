# A member pointer stored by a callee keeps its subobject

`set` stores `&p->first` through `h->link` and says so. The caller reloads
the field and reads one element past it, at `second`'s address, which it
can view; the reloaded pointer still designates only `first`.

```c filename=stored_member.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
void set(struct Pair* p, struct Holder* h) { h->link = &p->first; }
int32 probe(struct Pair* p, struct Holder* h) { set(p, h); return h->link[1]; }
```

```click
verifying "stored_member.c";
void set(struct Pair* p, struct Holder* h) {
    owns h->link;
    ensures h->link == &p->first;
} by { execute(); simp(); }

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
