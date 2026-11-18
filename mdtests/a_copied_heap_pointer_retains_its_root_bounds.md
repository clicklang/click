# A pointer copied into a field retains its root bounds

A complete pointer-value equality carries the allocation's root bounds as well
as its address. Folding a typed memory clause may use that equality without
replacing the logical read by the stored pointer during lowering.

```c filename=copied_allocation_size.c
struct holder { int32* data; };
void use_copy(struct holder* out) {
    int32* p;
    p = malloc(4);
    if (p == 0) return;
    out->data = p;
    free(p);
}
```

```click
verifying "copied_allocation_size.c";
resource cell(p: int32*) { owns p[0..1]; }
void use_copy(struct holder* out) {
    owns *out;
} by {
    step();
    step();
    branch { true => { step(); } false => {} }
    step();
    have out->data == p;
    fold(cell(out->data));
    unfold(cell(out->data));
    step();
}
```

```expect
pass
```
