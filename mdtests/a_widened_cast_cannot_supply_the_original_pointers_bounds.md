# A widened cast cannot supply the original pointer's bounds

The byte view deliberately uses the enclosing-object escape. It does not
change the bounds of the original scalar member pointer used by C.

```c filename=cast.c
struct Pair { int32 first; int32 second; int32 third; };
int32* probe(int32* p) { return p + 2; }
int32* caller(struct Pair* p) { return probe(&p->first); }
```

```click
verifying "cast.c";
int32* probe(int32* p) {
    views ((uint8*)(void*)p)[0..12];
    ensures true;
} by { execute(); simp(); }
int32* caller(struct Pair* p) {
    views p->first;
    views p->second;
    views p->third;
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
