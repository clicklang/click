# Release two views on one borrow one at a time

```c filename=release.c
void package(int *p);

void update(int *p) {
    package(p);
    int value = p[1];
    p[0] = value;
}
```

```click
resource pair(p: int32*) {
    views p[0..1];
    views p[1..2];
}

verifying "release.c";

extern void package(int32* p) {
    views p[0..2] as input;
    produces pair(p) from input;
}

void update(int32* p) {
    owns p[0..2];
} by {
    step();
    unfold(pair(p));
    release_view(p[0..1]);
    step();
    release_view(p[1..2]);
    step();
    step_until(function.exit);
}
```

```expect
pass
```
