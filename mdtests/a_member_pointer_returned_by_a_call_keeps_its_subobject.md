# A member pointer returned by a call keeps its subobject

`first` returns `&p->first` and says so. The caller passes the result to a
reader whose clause claims two elements, the second of which is `p->second`.
The result designates only `first`, so the call is refused at the reader's
clause, though the caller can view both fields.

```c filename=returned_member.c
struct Pair { int32 first; int32 second; };
int32* first(struct Pair* p) { return &p->first; }
int32 second_of(int32* q) { return q[1]; }
int32 probe(struct Pair* p) { int32* q = first(p); return second_of(q); }
```

```click
verifying "returned_member.c";
int32* first(struct Pair* p) {
    ensures result == &p->first;
} by { execute(); simp(); }

int32 second_of(int32* q) {
    views q[0..2];
    ensures result == q[1];
} by { execute(); simp(); }

int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: the clause's range of 4-byte elements reaches outside the 4-byte subobject its pointer designates
```
