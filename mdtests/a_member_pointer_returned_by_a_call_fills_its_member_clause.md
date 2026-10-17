# A member pointer returned by a call fills a clause of its member

The control for `a_member_pointer_returned_by_a_call_keeps_its_subobject.md`.
The result adopts `&p->first`'s extent through the contract's equality, and
a reader's one-element clause lies exactly inside it. The extent's start is
spelled through `p`, not through the fresh result, so the clause check
respells the result at that start before measuring it.

```c filename=returned_member_control.c
struct Pair { int32 first; int32 second; };
int32* first(struct Pair* p) { return &p->first; }
int32 second_of(int32* q) { return q[0]; }
int32 probe(struct Pair* p) { int32* q = first(p); return second_of(q); }
```

```click
verifying "returned_member_control.c";
int32* first(struct Pair* p) {
    ensures result == &p->first;
} by { execute(); simp(); }

int32 second_of(int32* q) {
    views q[0..1];
    ensures result == q[0];
} by { execute(); simp(); }

int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->first;
} by { execute(); simp(); }
```

```expect
pass
```
