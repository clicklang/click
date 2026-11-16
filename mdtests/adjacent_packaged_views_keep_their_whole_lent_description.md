# Adjacent packaged views keep their whole lent description

The body declares two adjacent views. Its normalized frontier is the whole
range lent at entry, so that loan backs the returned composite. Consuming the
composite releases its hold and lets the caller write the recovered range.

```c filename=adjacent_packaged_views.c
void f(int32* p) {
    pack(p);
    drop(p);
    p[1] = 1;
}
```

```click
verifying "adjacent_packaged_views.c";

resource reader_pair(p: int32*) {
    views p[0..1];
    views p[1..2];
}

extern void pack(int32* p) {
    views p[0..2];
    produces reader_pair(p);
}

extern void drop(int32* p) {
    consumes reader_pair(p);
}

void f(int32* p) {
    owns p[0..2];
}
```

```expect
pass
```
