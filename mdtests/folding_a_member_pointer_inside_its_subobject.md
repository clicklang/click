# Folding a member pointer inside its subobject

Folding `one(q)` with `q = &p->first` claims `q[0..1]`, exactly the member
`q` designates, and unfolds back to it.

```c filename=fold.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) {
    int32* q = &p->first;
    return 0;
}
```

```click
verifying "fold.c";
resource one(q: int32*) {
    owns q[0..1];
}
int32 probe(struct Pair* p) {
    owns p->first;
    owns p->second;
    ensures result == 0;
} by {
    step();
    step();
    fold(one(q));
    unfold(one(q));
    execute();
    simp();
}
```

```expect
pass
```
