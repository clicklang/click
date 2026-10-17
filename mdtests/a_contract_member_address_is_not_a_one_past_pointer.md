# A contract member address is not a one-past pointer

A member address written in a contract designates the member, as the C
frontend's `&p->second` does (`design/pointer-subobject-extents.md`). So a
function returning `&p->first + 1` cannot promise `result == &p->second`:
the two share an address, but only the second may be dereferenced
(C11 6.5.6p7-p8). A caller would otherwise read through the result.
`second` returns the member's own address and keeps that promise.

```c filename=member_address.c
struct Pair { int32 first; int32 second; };
int32* one_past(struct Pair* p) { return &p->first + 1; }
int32* second(struct Pair* p) { return &p->second; }
```

```click
verifying "member_address.c";
int32* one_past(struct Pair* p) {
    views *p;
    ensures result == &p->second;
} by { execute(); simp(); }
int32* second(struct Pair* p) {
    views *p;
    ensures result == &p->second;
} by { execute(); simp(); }
```

```expect
fail: failed for `one_past.ensures_0`
```
