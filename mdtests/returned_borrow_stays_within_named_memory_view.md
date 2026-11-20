# A returned composite cannot use another view's coverage of the same owner

```c filename=narrow_borrow.c
void pack(int *p);
void use(int *p) { pack(p); }
```

```click
resource cursor(p: int32*) { views p[1..2]; }

verifying "narrow_borrow.c";

extern void pack(int32* p) {
    views p[0..1] as first;
    views p[0..2];
    produces cursor(p) from first;
}

void use(int32* p) {
    owns p[0..2];
} by {
    step();
}
```

```expect
fail: The selected input `views p[0]` does not establish coverage of `views p[1]`
```
