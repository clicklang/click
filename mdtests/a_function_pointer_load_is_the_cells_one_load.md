# A function-pointer load is the cell's one load

A function-pointer load uses the same address base as an object-pointer load
(`design/loads.md`, "Terms"): one cell at one version point is one load,
whatever type decodes it, and the type that decodes it is the term's. `set`
stores the callback `f` to the field `o->cb`, and both the ordinary and the
exact read of the field at exit read that store. `bump` writes only `o->n`,
so `o->cb` at exit reads the cell's entry load, the same load as `old(o->cb)`
and as `old(exact(o->cb))`.

```c filename=a_function_pointer_load_is_the_cells_one_load.c
struct ops { void (*cb)(int *p); int n; };
void set(struct ops *o, void (*f)(int *p)) { o->cb = f; o->n = 1; }
void bump(struct ops *o) { o->n = 2; }
```

```click
verifying "a_function_pointer_load_is_the_cells_one_load.c";
void set(struct ops* o, void (*f)(int32*)) {
    owns o->cb;
    owns o->n;
    ensures o->cb == f;
    ensures exact(o->cb) == f;
    ensures o->n == 1;
}

void bump(struct ops* o) {
    owns o->cb;
    owns o->n;
    ensures o->cb == old(o->cb);
    ensures o->cb == old(exact(o->cb));
    ensures o->n == 2;
}
```

```expect
pass
```
