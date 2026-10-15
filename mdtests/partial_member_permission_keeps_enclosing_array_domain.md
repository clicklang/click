# A selected array has its declared extent with partial byte permission

Viewing its first element promises the enclosing typed array exists. Forming
its one-past pointer needs that domain, but does not read the other elements.

```c filename=partial.c
struct Record { int32 values[4]; int32 tail; };
int32* finish(struct Record* p) { return p->values + 4; }
int32 nested(struct Record* p) { return p->values[0]; }
```

```click
verifying "partial.c";
int32* finish(struct Record* p) {
    views p->values[0];
    ensures address(result) == address(&p->tail);
} by { execute(); simp(); }
int32 nested(struct Record* p) {
    views p->values[0];
    ensures result == p->values[0];
} by { execute(); simp(); }
```

```expect
pass
```
