# Forming a pointer two past a scalar member is refused

C permits forming the one-past pointer of a scalar member, not one beyond
it, even when the address stays inside the enclosing struct and nothing is
read through it.

```c filename=probe.c
struct Pair { int32 first; int32 second; int32 third; };
int32* probe(struct Pair* p) { return &p->first + 2; }
```

```click
verifying "probe.c";
int32* probe(struct Pair* p) {
    ensures 1 == 1;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
