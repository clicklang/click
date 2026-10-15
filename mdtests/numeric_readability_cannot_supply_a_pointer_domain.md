# A derived viewability equation does not grant an input's domain

The helper's numeric precondition permits a one-past scalar pointer equal in
address to a readable sibling. Rewriting readability must not give the input
an array domain in which another addition would be defined.

```c filename=alias.c
struct Pair { int32 first; int32 second; };
void advance(int32* p, int32* q) { p = p + 1; }
void probe(struct Pair* p) { advance(&p->first + 1, &p->second); }
```

```click
verifying "alias.c";
void advance(int32* p, int32* q) {
    requires p == q;
    views *q;
    ensures true;
} by {
    have viewable(p[0..1]) by { rewrite(p == q); simp(); }
    execute(); simp();
}
void probe(struct Pair* p) {
    views p->first; views p->second;
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
