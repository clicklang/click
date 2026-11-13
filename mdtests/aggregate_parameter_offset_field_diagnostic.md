# A rejected by-value field claim names the field in the input object

```c filename=aggregate_parameter_offset_field_diagnostic.c
struct packet { int32 a; int32 b; };
int32 change(struct packet p) {
    int32* alias = &p.b;
    *alias = 5;
    return 0;
}
```

```click
verifying "aggregate_parameter_offset_field_diagnostic.c";
int32 change(struct packet p) {
    ensures p.b == 5;
}
```

```expect
fail: left side evaluated to old(p.b), right side evaluated to 5
```
