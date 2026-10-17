# A member pointer cannot claim its enclosing allocation bounds

Allocation tokens retain complete pointer identity. A scalar member at the
allocation base cannot obtain the enclosing object's token by address alone.

```c filename=allocation.c
struct Pair { int32 first; int32 second; int32 third; };
int32* probe(int32* p) { return p + 2; }
int32* caller(struct Pair* p) { return probe(&p->first); }
```
```click
verifying "allocation.c";
int32* probe(int32* p) {
 owns allocation(p, 12);
 ensures true;
} by { execute(); simp(); }
int32* caller(struct Pair* p) {
 owns allocation(p, sizeof(struct Pair));
 ensures true;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `owns allocation(p, 12)`
```
