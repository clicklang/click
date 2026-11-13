# A rejected by-value field claim names the field in the input object

```c filename=aggregate_parameter_nested_field_diagnostic.c
struct inner { int32 x; };
struct packet { int32 a; struct inner inner; };
int32 change(struct packet p) {
    int32* alias = &p.inner.x;
    *alias = 5;
    return 0;
}
```

```click
verifying "aggregate_parameter_nested_field_diagnostic.c";
int32 change(struct packet p) {
    ensures p.inner.x == 5;
}
```

```expect
fail: left side evaluated to old(p.inner.x), right side evaluated to 5
```
