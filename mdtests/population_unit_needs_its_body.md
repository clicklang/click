# A population unit requires its private body

Authority permits a membership change; it does not provide the member's
private memory. Producing a reference without `owns o[0..1]` is rejected.

```click
authorized resource ref(o: struct s*) {
    owns o->x;
}

verifying "mint.c";

int32 mint(struct s* o) {
    requires o != 0;
    owns authority(ref(o));
    produces 1 of ref(o);
} by {
    fold(1 of ref(o));
    execute();
    simp();
}
```

```c filename=mint.c
struct s { int32 x; };
int32 mint(struct s* o) { return 0; }
```

```expect
fail: missing resource fact `owns o->x`
```
