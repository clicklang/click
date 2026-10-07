# A contract exit cannot return a range and the composite that would hold it

The dual of the composite-beside-child case: `f` holds only `p[0..1]` and
claims to return it beside `wrap(p)`, whose body is that same range. One
cell cannot be both the returned range and the body of a returned
composite.

```c filename=child_composite.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "child_composite.c";
int32 f(int32* p) {
    owns p[0..1];
    produces wrap(p);
} by auto;
```

```expect
fail: missing resource fact
```
