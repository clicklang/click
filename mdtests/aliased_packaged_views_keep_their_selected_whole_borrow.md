# Separate aliased views retain their selected whole-range borrow

Bounded return normalization keeps the two written views separate. The selected
whole-range permission backs both pieces, and consuming the packaged owner
releases the hold so the caller can write the storage again.

```c filename=separate_packaged_views.c
void package(int32* p, int32* q);
void drop(int32* p, int32* q);
void use(int32* p, int32* q) { package(p, q); drop(p, q); p[1] = 7; }
```

```click
resource pair(p: int32*, q: int32*) {
    views p[0..1];
    views q[0..1];
}
verifying "separate_packaged_views.c";
extern void package(int32* p, int32* q) {
    requires q == p + 1;
    views p[0..2] as input;
    produces pair(p, q) from input;
}
extern void drop(int32* p, int32* q) {
    consumes pair(p, q);
}
void use(int32* p, int32* q) {
    requires q == p + 1;
    owns p[0..2];
}
```

```expect
pass
```
