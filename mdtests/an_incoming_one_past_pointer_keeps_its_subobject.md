# An incoming one-past pointer retains its selected member

```c filename=param.c
struct Pair { int32 first; int32 second; };
int32 probe(int32* q, struct Pair* p) { return *q; }
int32 caller(struct Pair* p) { return probe(&p->first + 1, p); }
```

```click
verifying "param.c";
int32 probe(int32* q, struct Pair* p) {
    views p->first;
    views p->second;
    requires q == &p->first + 1;
    ensures result == p->second;
} by { execute(); simp(); }
int32 caller(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: outside the subobject
```
