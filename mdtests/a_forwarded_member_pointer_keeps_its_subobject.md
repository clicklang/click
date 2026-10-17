# A forwarded member pointer keeps its subobject

`forward` receives `&p->first` with a one-element clause and passes it to
`reach`, which has no clause on it but views `p->second`. `reach` cannot
read `q[1]`: nothing it holds says what `q` designates.

```c filename=forwarded_member.c
struct Pair { int32 first; int32 second; };
int32 reach(struct Pair* p, int32* q) { return q[1]; }
int32 forward(struct Pair* p, int32* q) { return reach(p, q); }
int32 top(struct Pair* p) { return forward(p, &p->first); }
```

```click
verifying "forwarded_member.c";
int32 reach(struct Pair* p, int32* q) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32 forward(struct Pair* p, int32* q) {
    views q[0..1];
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32 top(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views q[1]`
```
