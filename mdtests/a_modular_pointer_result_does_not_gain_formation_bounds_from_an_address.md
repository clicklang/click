# A modular pointer result does not gain formation bounds from an address

The result's numeric address alone cannot transport the member's bounds.

```c filename=probe.c
struct Pair { int32 first; int32 second; int32 third; };
int32* member(struct Pair* x) { return &x->first; }
int32* caller(struct Pair* x) { return member(x) + 2; }
```

```click
verifying "probe.c";
int32* member(struct Pair* x) {
    views x->first;
    ensures address(result) == address(&x->first);
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
