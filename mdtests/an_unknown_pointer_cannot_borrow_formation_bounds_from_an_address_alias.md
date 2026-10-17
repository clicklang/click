# An unknown pointer cannot borrow formation bounds from an address alias

The callee receives a scalar member and a wider view at the same address.
Returning the displaced pointer already requires valid formation bounds.

```c filename=probe.c
struct Pair { int32 first; int32 second; int32 third; };
int32* probe(int32* p, int32* q) { return p + 2; }
int32* caller(struct Pair* x) {
    return probe(&x->first, (int32*)(void*)x);
}
```

```click
verifying "probe.c";
int32* probe(int32* p, int32* q) {
    views q[0..3];
    requires address(p) == address(q);
    ensures true;
} by { execute(); simp(); }
int32* caller(struct Pair* x) {
    views x->first;
    views x->second;
    views x->third;
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
