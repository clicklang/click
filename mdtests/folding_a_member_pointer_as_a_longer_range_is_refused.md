# Folding a member pointer as a longer range is refused

Folding `two(q)` with `q = &p->first` claims `q[0..2]` through a pointer that
designates only `first`. The caller owns both members, but the fold may not
gather `second` under `first`'s pointer.

```c filename=fold.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) {
    int32* q = &p->first;
    return 0;
}
```

```click
verifying "fold.c";
resource two(q: int32*) {
    owns q[0..2];
}
int32 probe(struct Pair* p) {
    owns p->first;
    owns p->second;
    ensures result == 0;
} by {
    step();
    step();
    fold(two(q));
    unfold(two(q));
    execute();
    simp();
}
```

```expect
fail: reaches outside the 4-byte subobject its pointer designates
```
