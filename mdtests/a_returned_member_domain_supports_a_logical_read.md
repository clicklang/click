# A returned member domain supports a resource fold and logical read

The call returns a complete pointer equal to the nested member address.
Folding a one-cell resource through the local and naming a logical read
through the recorded call result retain the corresponding source terms.
Numeric address equality alone cannot supply the complete pointer relationship.

```c filename=member_domain.c
struct Item { int32 value; };
struct Outer { int32 first; struct Item child; };
int32* child(struct Outer* p) { return &p->child.value; }
int32 probe(struct Outer* p) { int32* q = child(p); return *q; }
```

```click
verifying "member_domain.c";
resource cell(q: int32*) { owns q[0]; }
int32* child(struct Outer* p) {
    views p->child.value;
    ensures result == &p->child.value;
}
int32 probe(struct Outer* p) {
    owns p->child.value;
    ensures result == p->child.value;
} by {
    step(); step(); step();
    have at(call(0).exit, call(0).result) == &p->child.value by { known(); }
    fold(cell(q));
    unfold(cell(q));
    have at(call(0).exit, call(0).result)[0] == p->child.value by {
        rewrite(at(call(0).exit, call(0).result), &p->child.value);
        known();
    }
    step();
}
```

```expect
pass
```
