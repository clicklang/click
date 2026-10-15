# Member pointers stay usable inside their subobject

A member's address designates the member: arithmetic and access inside it
are unaffected by its narrower extent. `+ 0` reads the member itself, the
one-past pointer may be formed and returned (it shares only its address with
`second`), a member array is traversed
through its decayed pointer, a nested member is read through its own
address, and a member pointer stored in and reloaded from a field still
reads the member.

```c filename=members.c
struct Pair { int32 first; int32 second; };
struct Rec { int32 arr[4]; int32 tail; };
struct Outer { int32 tag; struct Pair inner; };
struct Holder { int32* link; };

int32 same(struct Pair* p) { return *(&p->first + 0); }
int32* one_past(struct Pair* p) { return &p->first + 1; }
int32 second(struct Pair* p) { return *(&p->second); }
int32 element(struct Rec* r) { int32* q = r->arr; return *(q + 3); }
int32 nested(struct Outer* o) { int32* q = &o->inner.second; return *q; }
int32 stored(struct Pair* p, struct Holder* h) {
    h->link = &p->first;
    int32* q = h->link;
    return *q;
}
```

```click
verifying "members.c";
int32 same(struct Pair* p) {
    views p->first;
    ensures result == p->first;
} by { execute(); simp(); }
int32* one_past(struct Pair* p) {
    ensures address(result) == address(&p->second);
} by { execute(); simp(); }
int32 second(struct Pair* p) {
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32 element(struct Rec* r) {
    views r->arr[0..4];
    ensures result == r->arr[3];
} by { execute(); simp(); }
int32 nested(struct Outer* o) {
    views o->inner.second;
    ensures result == o->inner.second;
} by { execute(); simp(); }
int32 stored(struct Pair* p, struct Holder* h) {
    views p->first;
    owns h->link;
    ensures result == p->first;
} by { execute(); simp(); }
```

```expect
pass
```
